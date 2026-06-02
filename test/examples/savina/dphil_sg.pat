
interface ForkMb {
  Take(PhilMb!),
  Drop(PhilMb!)
}

interface PhilMb {
  Ack()
}

def forkDown(self: ForkMb?): Unit {
  guard self: (Take + Drop)* {
    free -> ()
    receive Take(philMb) from self ->
      philMb ! Ack();
      forkUp(self)
    receive Drop(philMb) from self ->
      forkDown(self)
  }
}

def forkUp(self: ForkMb?): Unit {
  guard self: (Take + Drop)* {
    free -> ()
    receive Take(philMb) from self ->
      forkUp(self)
    receive Drop(philMb) from self ->
      philMb ! Ack();
      forkDown(self)
  }
}
 
def phil(self: PhilMb?, left: ForkMb!, right: ForkMb!, name: Int): Unit {
  # Think for a while and then try to take the forks.
  left ! Take(self);
  guard self: Ack { # It is also possible to use the pattern Ack + 1 here and in the guard blocks below.
    free -> ()
    receive Ack() from self ->
      right ! Take(self);
      guard self: Ack {
        free -> ()
        receive Ack() from self ->
	     # Eat for a while and then drop the forks.
	     left ! Drop(self);
	     guard self: Ack {
            free -> ()
	     receive Ack() from self ->
	       right ! Drop(self);
	       guard self: Ack {
              free -> ()
	         receive Ack() from self ->
		      phil(self, left, right, name)
            }
          }
      }
  }
}

def main(): Unit {
  let fork1Mb = new [ForkMb] in spawn { forkDown(fork1Mb) };
  let fork2Mb = new [ForkMb] in spawn { forkDown(fork2Mb) };
  let fork3Mb = new [ForkMb] in spawn { forkDown(fork3Mb) };
  let fork4Mb = new [ForkMb] in spawn { forkDown(fork4Mb) };
  let fork5Mb = new [ForkMb] in spawn { forkDown(fork5Mb) };

  let plato =      new [PhilMb] in spawn { phil(plato,     fork1Mb, fork2Mb, 1) };
  let socrates =   new [PhilMb] in spawn { phil(socrates,  fork2Mb, fork3Mb, 2) };
  let aristotle =  new [PhilMb] in spawn { phil(aristotle, fork3Mb, fork4Mb, 3) };
  let descartes =  new [PhilMb] in spawn { phil(descartes, fork4Mb, fork5Mb, 4) };
  let kant =       new [PhilMb] in spawn { phil(kant,      fork1Mb, fork5Mb, 5) } # Reversed forks to avoid deadlock
}

main()
