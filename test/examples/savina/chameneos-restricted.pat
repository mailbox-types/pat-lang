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
  Request(ChameneosMb!),
  Leave()
}

interface ChameneosMb {
  BeActive(ChameneosMb!, MallMb!),
  BePassive(MallMb!),
  Play(Int,ChameneosMb!),
  Respond(Int)
}

## A chameneos with its colour represented by 0, 1 or 2
def chameneos(self: ChameneosMb?, colour: Int, mall: MallMb!Request) : Unit {
  print("Training and eating honeysuckle");
  mall ! Request(self);
  guard self: BeActive + (BePassive . Play) {
    receive BeActive(other, mallNext) from self -> 
      chameneos_active(self, colour, other, mallNext)
    receive BePassive(mallNext) from self ->
      chameneos_passive(self, colour, mallNext)
  }
}

## The chameneos has been told to play the active role
def chameneos_active(self: ChameneosMb?, colour: Int, other: ChameneosMb!, mall: MallMb!Leave) : Unit {
  other ! Play(colour,self);
  guard self: Respond {
    receive Respond(c) from self ->
      free(self);
      chameneos_transform(colour, c, mall)
  }
}
    
## The chameneos has been told to play the passive role
def chameneos_passive(self: ChameneosMb?, colour: Int, mall: MallMb!) : Unit {
  guard self: Play {
    receive Play(c,other) from self ->
      print("Entering the mall.");
      other ! Respond(colour);
      free(self);
      chameneos_transform(colour, c, mall)
  }
}

## When the chameneos knows the colour of its partner, it can work out whether to change colour.
def chameneos_transform(colour: Int, other_colour: Int, mall: MallMb!) : Unit {
  if (colour == other_colour) {
    print("Playing but not changing colour.");
    print("Leaving the mall.");
    mall ! Leave()
  } else {
    print("Changing colour.");
    print("Leaving the mall.");
    mall ! Leave()
  }
}

## The mall, intially empty
def mall(self: MallMb?) : Unit { 
  guard self: Request . Request {
    receive Request(idFirst) from self ->
      idFirst ! BePassive(self);
      mall_one(self,idFirst)
  }
}

## The mall with one chameneos inside
## This isn't typable because both id and idSecond are in scope with the same interface.
## But how else can one chameneos be informed of the other's existence?
def mall_one(self: MallMb?, id: ChameneosMb!) : Unit {
  guard self : Request . Leave {
    receive* Request(idSecond) from self ->
      idSecond ! BeActive(id, self);
      mall_two(self)
  }
}

## The mall with two chameneos inside
def mall_two(self: MallMb?) : Unit {
  guard self: Leave . Leave {
    receive Leave() from self ->
      guard self: Leave {
        receive Leave() from self ->
          free(self)
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
  launch(1, m)
}

main(10)








