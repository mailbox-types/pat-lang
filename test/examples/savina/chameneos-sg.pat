### The chameneos example from "Chameneos, a Concurrency Game for Java, Ada and Others"
### by Claude Kaiser and Jean-Francois Pradat-Peyre

### A chameneos (it seems to be both singular and plural) is an animal that can be red, yellow or blue.
### Most of the time a chameneos lives a quiet existence of training and eating honeysuckle.
### From time to time, a chameneos can request to enter the mall in order to play a game of pall mall
### with another chameneos. The mall allows at most two chameneos to enter at a time.
### When two chameneos play, if their colours are different then they both change to the third colour.
### To avoid deadlock between the chameneos, they are told whether they are active or passive.
### The active chameneos in the pair sends a Play message to the passive chameneos, who waits to receive it.
### After playing, the chameneos leave the mall.

interface MallMb {
  Request(ChameneosMb!)
}

interface ChameneosMb {
  BeActive(ChameneosMb!, MallSignalMb!),
  BePassive(MallSignalMb!),
  Play(Int,ChameneosMb!),
  Lonely(),
  Respond(Int)
}

interface MallSignalMb {
  Leave()
}

## A chameneos with its colour represented by 0, 1 or 2
def chameneos(self: ChameneosMb?, colour: Int, mall: MallMb!) : Unit { ## was MallMB!(Request*)
  print("Training and eating honeysuckle");
  mall ! Request(self);
  guard self: BeActive + (BePassive . (Lonely + Play)) { ## Where does Lonely come from?
    receive BeActive(other, mallSignal) from self -> 
      chameneos_active(self, colour, other, mall, mallSignal)  ## Why do we have both mall and mallSignal?
    receive BePassive(mallSignal) from self ->
      chameneos_passive(self, colour, mall, mallSignal)
  }
}

## The chameneos has been told to play the active role
def chameneos_active(self: ChameneosMb?, colour: Int, other: ChameneosMb!, mall: MallMb!, mallSignal: MallSignalMb!) : Unit { ## was MallSignalMb!Leave
  other ! Play(colour, self);
  guard self: Respond {
    receive Respond(c) from self ->
      chameneos_transform(self, colour, c, mall, mallSignal)
  }
}
    
## The chameneos has been told to play the passive role
def chameneos_passive(self: ChameneosMb?, colour: Int, mall: MallMb!, mallSignal: MallSignalMb!) : Unit { ## was MallMb!(Request*), MallSignalMb!Leave
  guard self: Play + Lonely {
    receive Lonely() from self ->
        mallSignal ! Leave();
        free(self)
    receive Play(c, other) from self ->
      print("Entering the mall.");
      other ! Respond(colour);
      chameneos_transform(self, colour, c, mall, mallSignal)
  }
}

## When the chameneos knows the colour of its partner, it can work out whether to change colour.
def chameneos_transform(self: ChameneosMb?, colour: Int, other_colour: Int, mallMb: MallMb!, mallSignal: MallSignalMb!) : Unit { ## was MallMb!(Request*), MallSignalMb!Leave
  if (colour == other_colour) {
    print("Playing but not changing colour.");
    print("Leaving the mall.");
    mallSignal ! Leave();
    chameneos(self, colour, mallMb)
  } else {
    print("Changing colour.");
    print("Leaving the mall.");
    mallSignal ! Leave();
    chameneos(self, 3 - colour - other_colour, mallMb)
  }
}

## The mall, intially empty
def mall(self: MallMb?) : Unit { 
  guard self: Request* { ## We don't receive Leave on self; it comes to a different mailbox.
    free -> ()
    receive Request(idFirst) from self ->
      let signalMb = new[MallSignalMb] in  ## Create separate mailbox for Leave messages. Why?
      idFirst ! BePassive(signalMb);       ## The first chameneos to enter the mall becomes the passive partner.
      mall_one(self, idFirst, signalMb)
  }
}

## The mall with one chameneos inside
def mall_one(self: MallMb?, idFirst: ChameneosMb!, signalMb: MallSignalMb?) : Unit {
  guard self : Request*  {
    empty(self) ->    ## Detect that a second request will never arrive. (How?)
        idFirst ! Lonely();  ## Tell the first chameneos that it shouldn't wait for a partner.
        guard signalMb : Leave {  ## Wait for the first chameneos to leave.
            receive Leave() from signalMb -> free(signalMb)  ## Now we don't need signalMb any more; another one will be created if necessary.
        };
        free(self)
    receive* Request(idSecond) from self ->     ## receive* is needed here because both idFirst and idSecond are in scope.
      idSecond ! BeActive(idFirst, signalMb);   ## The second chameneos to enter the mall becomes the active partner.
      mall_two(self, signalMb)
  }
}

## The mall with two chameneos inside
def mall_two(self: MallMb?, signalMb: MallSignalMb?) : Unit {
  guard signalMb : Leave . Leave { ## The use of signalMb allows us to know exactly what the contents can be here.
    receive Leave() from signalMb ->
      guard signalMb: Leave {
        receive Leave() from signalMb ->
          free(signalMb);
          mall(self)
      }
  }
}

## Launch several chameneos processes with a given colour
def launch(colour: Int, mall: MallMb!) : Unit {
    spawn { chameneos(new [ChameneosMb], colour, mall) }
}

## Top level
def main(n: Int) : Unit {
  let m = new [MallMb] in
  spawn { mall(m) } ;
  launch(0, m);
  launch(1, m);
  launch(2, m)
}

main(10)








