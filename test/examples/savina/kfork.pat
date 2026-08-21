### Adapted from Savina/fjthrput.
###
### Models the creation of n actors that are given a number of messages, for
### each of which, a computation is performed. The benchmark is parameterized by
### the number of actor processes. Since the array type is not available in
### Pat, we fix the number of actor processes to 3.

interface ActorMb {
  Packet()
}

## Actor processes handling the packet requests.
def actor(self: ActorMb?): Unit {
  guard self: Packet* {
    free ->
      print("freed")
    receive Packet() from self ->
      let dummy = fact(rand(10)) in
      actor(self)
  }
}

## Computes the factorial of n.
def fact(n: Int): Int {
  if (n <= 0) {
    1
  }
  else {
    n * (fact(n - 1))
  }
}

## Sends the given number of messages to the specified actor mailbox.
def flood(numMessages: Int, actorMb: ActorMb!): Unit {
  print(intToString(numMessages));
  if (numMessages <= 0) {
    ()
  }
  else {
    actorMb ! Packet();
    flood(numMessages - 1, actorMb)
  }
}

## Launcher.
def main(): Unit {

  let actorMb1 = new [ActorMb] in
  spawn { actor(actorMb1) };

  let actorMb2 = new [ActorMb] in
  spawn { actor(actorMb2) };

  let actorMb3 = new [ActorMb] in
  spawn { actor(actorMb3) };

  flood(100, actorMb1);
  flood(100, actorMb2);
  flood(100, actorMb3)
}

main()
