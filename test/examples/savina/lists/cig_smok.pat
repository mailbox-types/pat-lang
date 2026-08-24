### Adapted from Savina/cigsmok.
###
### A benchmark modelling n smokers and one arbiter that decides which smoker to
### allow to smoke. The benchmark is parameterized by the number of smoker
### processes.

interface ArbiterMb {
  Start(Int),
  StartedSmoking()
}

interface SmokerMb {
  StartSmoking(Int),
  Exit()
}

def create_smokers(self: ArbiterMb?, moreSmokers: Int, acc: List(SmokerMb!)): (ArbiterMb? * List(SmokerMb!)) {
    if (moreSmokers == 0) {
        (self, acc)
    }
    else {
        let newSmoker = new [SmokerMb] in
            spawn { smoker(newSmoker, self) };
            create_smokers(self, moreSmokers - 1, (newSmoker :: acc))
        }
}

## Arbiter process handling the creation of smokers and launching of main loop.
def arbiter(self: ArbiterMb?, numRounds: Int): Unit {

  guard self: Start . (StartedSmoking*) {
    receive Start(numSmokers) from self ->

       let (self, smokerMbs) = create_smokers(self, numSmokers, (nil : List(SmokerMb!))) in

        let smokerMbs = notify_smoker(numSmokers, smokerMbs) in
        arbiter_loop(self, numSmokers, numRounds, smokerMbs)
  }
}

## Randomly chooses the smoker and requests it to smoke.
def notify_smoker(numSmokers: Int, smokerMbs: List(SmokerMb!)): List(SmokerMb!) {

  let smokerId = rand(numSmokers - 1) in
  let sleepTimeMs = 1000 in

  notify_aux(smokerId, sleepTimeMs, smokerMbs)
}

def notify_aux(choice: Int, time: Int, smokerMbs: List(SmokerMb!)): List(SmokerMb!) {
if (choice == 0) {
    case smokerMbs : List(SmokerMb!)  of {
        nil -> nil
        | (mb :: mbs) ->
            mb ! StartSmoking(rand(time));
            (mb :: mbs)
    }
}
else {
    case smokerMbs : List(SmokerMb!) of {
        nil -> nil
        | (mb :: mbs) ->
            let smokerMbs = notify_aux(choice - 1, time, mbs) in
            (mb :: smokerMbs)
    }
}
}

## Notifies all smokers to terminate.
def notify_smoker_exit(smokerMbs: List(SmokerMb!)): List(SmokerMb!) {
    case smokerMbs : List(SmokerMb!) of {
        nil -> nil
        | (mb :: mbs) ->
            mb ! Exit();
            notify_smoker_exit(mbs)
        }
}

## Arbiter process main loop issuing start smoking requests and handling started
## smoking replies.
def arbiter_loop(self: ArbiterMb?, numSmokers: Int, numRounds: Int, smokerMbs: List(SmokerMb!)): Unit {
  guard self: StartedSmoking* {
    free ->
      case smokerMbs : List(SmokerMb!) of {
      nil -> ()
      | (a :: as) -> ()
  }
    receive StartedSmoking() from self ->

      # The if here introduces the internal choice, which means that on the
      # receiver side I might or might not receive the message. In this case,
      # the smoker might or might nor receive the Exit message, and must either
      # use (Exit + 1) or (*Exit) in its pattern.

      if (numRounds <= 0) {
        let smokerMbs = notify_smoker_exit(smokerMbs) in
            arbiter_loop(self, numSmokers, numRounds - 1, smokerMbs)
      }
      else {
        let smokerMbs = notify_smoker(numSmokers, smokerMbs) in
            arbiter_loop(self, numSmokers, numRounds - 1, smokerMbs)
      }

      # Arbiter needs to service all requests before, even if it has sent the
      # Exit messages to smokers. Remember that smokers may still be processing
      # StartSmoking messages, but the arbiter has already issued Exit messages
      # and it still needs to await all the StartedSmoking replies before
      # terminating. This is why we do not have an exit_arbiter flush function.

  }
}

## Smoker process main loop handling start smoking requests and issuing started
## smoking replies to/from the arbiter.
def smoker(self: SmokerMb?, arbiterMb: ArbiterMb!): Unit {
  # Smoker may be asked to smoke more than once, or none. This is why the *.
  guard self: (StartSmoking*) . (Exit*) {
    free ->
      () # Since the smoker might not even receive an Exit/StartSmoking message due to the if condition above.
    receive StartSmoking(ms) from self ->
      arbiterMb ! StartedSmoking();
      sleep(ms);
      smoker(self, arbiterMb)
    receive Exit() from self ->
      smoker_exit(self)
  }
}

## Smoker process exit procedure that flushes potential residual messages.
def smoker_exit(self: SmokerMb?): Unit {
  guard self: (StartSmoking*) . (Exit*) {
    free -> () # In case I have one or more Exit/StartSmoking messages due to the if condition above.
    receive StartSmoking(ms) from self ->
      smoker_exit(self)
    receive Exit() from self ->
      smoker_exit(self)
  }
}

## Launcher.
def main(numSmokers : Int): Unit {

  let arbiterMb = new [ArbiterMb] in
  spawn { arbiter(arbiterMb, 10) };

  arbiterMb ! Start(numSmokers)
}

main(5)
