### Adapted from Savina/big.
###
### A benchmark that implements a many-to-many message passing scenario. Several
### processes are spawned, each of which sends a ping message to the others, and
### responds with a pong message to any ping message it receives. The benchmark
### is parameterized by the number of processes.

interface ActorMb {
  Ping(Int),
  Pong(Int),
  Neighbors(ActorMb!, ActorMb!)
}

interface ExitMb {
  Exit()
}

interface SinkMb {
  Done(),
  Actors(List(ExitMb!))
}

## Actor process handling the launching of main loop.
def actor(self: ActorMb?, exitMb : ExitMb?, id: Int, sinkMb: SinkMb!): Unit {
  guard self: Neighbors . (Pong + Ping)*  {
    receive Neighbors(actorMb1, actorMb2) from self ->
      actor_loop(self, exitMb, id, sinkMb, 100, actorMb1, actorMb2)
  }
}

## Blocks actor process and awaits termination message.
def await_exit(exitMb: ExitMb?): Unit {
    guard exitMb : Exit {
        receive Exit() from exitMb ->
          free(exitMb)
    }
}

## Actor process main loop issuing ping requests and handling pong replies.
def actor_loop(self: ActorMb?, exitMb: ExitMb?, id: Int, sinkMb: SinkMb!, numPings: Int, actorMb1: ActorMb!, actorMb2: ActorMb!): Unit {
  guard self: (Ping + Pong)* {
    free ->
      await_exit(exitMb)
    receive Ping(pingerId) from self ->

      # Reply to ping.
      send_pong(id, pingerId, actorMb1, actorMb2);
      actor_loop(self, exitMb, id, sinkMb, numPings, actorMb1, actorMb2)

    receive Pong(pongerId) from self ->

      if (numPings <= 0) {

        # No more pongs to issue.
        sinkMb ! Done();
        actor_exit(self);
        await_exit(exitMb)
      }
      else {

        # Issue ping to random participant.
        send_ping(id, actorMb1, actorMb2);
        actor_loop(self, exitMb, id, sinkMb, numPings - 1, actorMb1, actorMb2)
      }
  }
}

## Actor process exit procedure that flushes potential residual messages.
def actor_exit(self: ActorMb?): Unit {
  guard self: (Ping*) . (Pong*) {
    free -> ()
    receive Ping(pingerId) from self ->
      actor_exit(self)
    receive Pong(pongerId) from self ->
      actor_exit(self)
  }
}

## Replies to ping messages via a pong issued to the specified actor ID.
def send_pong(id: Int, pingerId: Int, actorMb1: ActorMb!, actorMb2: ActorMb!): Unit {

  # We are not synchronising here, but using IDs, which loses information. This
  # makes the type checker think that it might not receive the pong reply. Thus,
  # the type of the mailbox would be ?(Pong + 1).
  if (pingerId == 1) {
    actorMb1 ! Pong(id)
  }
  else {
    actorMb2 ! Pong(id)
  }
}

## Randomly issues a ping message to one of the participating actors.
def send_ping(id: Int, actorMb1: ActorMb!, actorMb2: ActorMb!): Unit {
  let pongerId = rand(2) in
  if (pongerId == 1) {
    actorMb1 ! Ping(id)
  } else {
    actorMb2 ! Ping(id)
  }
}

## Sink process that coordinates actor termination.
def sink(self: SinkMb?, exitMbs : List(ExitMb!)): Unit {
  guard self: Done* {
    free ->
      # Notify all actors. Placing the sends in this clause ensures that
      # each actor is notified once.
      notifyExits(exitMbs)
    receive Done() from self ->
        sink(self, exitMbs)
  }
}

def notifyExits(exitMbs : List(ExitMb!)): Unit {
    caseL exitMbs : List(ExitMb!) of {
    nil -> ()
  | (y :: ys) ->
        y ! Exit();
        notifyExits(ys)
    }
}


## Launcher.
def main(): Unit {

  let sinkMb = new [SinkMb] in

  let actorMb1 = new [ActorMb] in # actorMb1: ?1
  let actorMb2 = new [ActorMb] in # actorMb2: ?1
  let actorMb3 = new [ActorMb] in # actorMb3: ?1
  let exitMb1 = new [ExitMb] in # exitMb1: ?1
  let exitMb2 = new [ExitMb] in # exitMb2: ?1
  let exitMb3 = new [ExitMb] in # exitMb3: ?1

  spawn { actor(actorMb1, exitMb1, 1, sinkMb) };
  spawn { actor(actorMb2, exitMb2, 2, sinkMb) };
  spawn { actor(actorMb3, exitMb3, 3, sinkMb) };

  let xs = (exitMb1 :: (exitMb2 :: (exitMb3 :: (nil : List(ExitMb!))))) in
  spawn { sink(sinkMb, xs) };

  actorMb1 ! Neighbors(actorMb2, actorMb3); # actorMb1: ?Neighbors
  actorMb2 ! Neighbors(actorMb1, actorMb3); # actorMb2: ?Neighbors
  actorMb3 ! Neighbors(actorMb1, actorMb2); # actorMb3: ?Neighbors

  actorMb1 ! Pong(0); # actorMb1: ?Neighbors . Pong
  actorMb2 ! Pong(0); # actorMb2: ?Neighbors . Pong
  actorMb3 ! Pong(0) # actorMb2: ?Neighbors . Pong
}

main()
