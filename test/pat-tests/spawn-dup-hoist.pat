### Regression test for reference counting across 'spawn'.
###
### The duplication that a spawned body needs from the enclosing scope must be
### performed by the parent thread, before the child is created. Here the use of
### 'mb' sits behind a let-binding, so a translation that only hoists a 'dup'
### appearing at the very front of the body would leave it inside the child --
### and the parent would consume its own reference with the send before the
### child is ever scheduled.

interface ActorMb {
  Packet()
}

def actor(self: ActorMb?): Unit {
  guard self: Packet* {
    free ->
      print("freed")
    receive Packet() from self ->
      actor(self)
  }
}

## Burns enough interpreter steps that the spawned thread is descheduled before
## it reaches the use of 'mb'.
def burn(n: Int): Int {
  if (n <= 0) {
    0
  }
  else {
    burn(n - 1)
  }
}

def main(): Unit {
  let mb = new [ActorMb] in
  spawn { let d = burn(50) in actor(mb) };
  mb ! Packet()
}

main()
