### Adapted from Savina/fjthrput.
###
### Models the creation of n actors that are given a number of messages, for
### each of which, a computation is performed. The benchmark is parameterized by
### the number of actor processes.

interface ActorMb {
  Packet()
}

## Actor processes handling the packet requests.
def actor(self: ActorMb?): Unit {
  guard self: Packet* {
    free ->
      ()
    receive Packet() from self ->
      let dummy = fact(rand(100000)) in
      actor(self)
  }
}

## Computes the factorial of n.
def fact(n: Int): Int {
  if (n <= 0) {
    1
  }
  else {
    n * (fact(n - 1))
  }
}

## Sends the given number of messages to the specified actor mailbox.
def flood(numMessages: Int, actorMb: ActorMb!): Unit {
  if (numMessages <= 0) {
    ()
  }
  else {
    actorMb ! Packet();
    flood(numMessages - 1, actorMb)
  }
}

def spawnActors(numActors: Int, acc: List(ActorMb!)): List(ActorMb!) {
    if (numActors <= 0) {
        acc
    } else {
        let newActor = new[ActorMb] in
        spawn { actor(newActor) };
        spawnActors(numActors - 1, (newActor :: acc))
    }
}

def floodActors(numMessages: Int, actorMbs: List(ActorMb!)): Unit {
    caseL actorMbs : List(ActorMb!) of {
        nil -> ()
      | (a :: as) ->
            flood(numMessages, a);
            floodActors(numMessages, as)
        }
}

## Launcher.
def main(numActors: Int): Unit {

  let actorMbs = spawnActors(numActors, nil) in
  floodActors(1000, actorMbs)
}

main(3)
