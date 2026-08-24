### Adapted from Savina/banking.
###
### A benchmark that implements a request-reply chain passing scenario. Several
### account processes are spawned, each of which may be sent a credit request
### by the central teller process. The benchmark is parameterized by the number
### of account processes.

interface TellerMb {
  Start(),
  Reply()
}

interface AccountMb {
  Debit(AccountMb!, Int),
  Credit(TellerMb!, Int, AccountMb!),
  Done(),
  Stop()
}

def spawnAccounts(numsAccounts: List(Int), soFar: Int, acc: List(AccountMb!)) : List(AccountMb!) {
  case numsAccounts of {
    nil -> acc
    | (n :: ns) ->
        let accountMb = new [AccountMb] in
        spawn { account(accountMb, soFar, n)};
        spawnAccounts(ns, soFar + 1, (accountMb :: acc))
    }
  }

## Teller process handling the creation of account processes and launching of
## main loop.
def teller(self: TellerMb?, numAccounts : Int, numsAccounts: List(Int)): Unit {

  let accountMbs = spawnAccounts(numsAccounts, 1, (nil : List(AccountMb!))) in
  guard self: Start {
    receive Start() from self ->

      # Note. Even if the randomization of message sending is performed in a
      # different processes, there is no risk of a race condition where the
      # messages are sent to a non-existing mailbox. This is because, as can be
      # gleaned above, mailboxes are created in sequential fashion within this
      # (i.e., the teller) process.
      spawn { generate_work(self, numAccounts, accountMbs) } ;
      teller_loop(self, accountMbs)
  }
}

## Randomly chooses the source account.
def generate_work(tellerMb: TellerMb!, numAccounts: Int, accs : List(AccountMb!)): Unit {

  # Randomly choose source account from which the funds shall be taken.
  let sourceId = rand(numAccounts - 1) in # -1 because rand() is 0-indexed.

  let (choice, rest) = pick(accs, sourceId, (nil : List(AccountMb![R]))) in
  choose_dst_acc(tellerMb, numAccounts, choice, rest)
}

def pick(accs : List(AccountMb![R]), index : Int, rest : List(AccountMb![R])) : ((Unit + AccountMb![R]) * List(AccountMb![R])) {
if (index == 0) {
    case accs of {
        nil -> let x = () in (inl(x) : (Unit + AccountMb!), rest)
        | (a :: as) -> (inr(a) : (Unit + AccountMb!), append(rest, as))
    }}
else {
    case accs of {
        nil ->  let x = () in (inl(x) : (Unit + AccountMb!), rest)
        | (a :: as) -> pick(as, index - 1, (a :: rest))
    }}
}

def append(l1 : List(AccountMb![R]), l2: List(AccountMb![R])) : List(AccountMb![R]) {
    case l1 of {
        nil -> l2
        | (a :: as) -> append(as, (a :: l2))
    }
}

## Randomly chooses the destination account and issues a credit request. The
## function ensures that the source and destination account are different.
def choose_dst_acc(tellerMb: TellerMb!, numAccounts: Int, srcAccount: (Unit + AccountMb![R]), dstAccountMbs : List(AccountMb![R])) : Unit {

    # Randomly choose destination account to which funds shall be deposited. -2
    # because rand() is 0-indexed, and because we do not include the source
    # account in the random choice (i.e., the source account is not permitted to
    # send funds to itself).
    let dstAccountId = rand(numAccounts - 2) in
  
    let (dstAccount, rest) =
        pick(dstAccountMbs, dstAccountId, (nil : List(AccountMb![R])))
    in
    let amount = rand(200) in
    case srcAccount of {
        inl(u1) ->
            case dstAccount of {
                  inl(u2) -> ()
                | inr(d)  -> ()
            }
        | inr(a) ->
            case dstAccount of {
                  inl(u) -> ()
                | inr(d) -> d ! Credit(tellerMb, amount, a)
        }
    }
}

## Teller process main loop handling replies from accounts.
def teller_loop(self: TellerMb?, accountMbs : List(AccountMb!)): Unit {
  guard self: Reply* {
    free ->
      # All credit requests serviced. Stop accounts.
      stopAccounts(accountMbs)
    receive Reply() from self ->
      teller_loop(self, accountMbs)
  }
}

def stopAccounts(accs: List(AccountMb!)) : Unit {
    case accs of {
        nil -> ()
        | (a :: as) ->
            a ! Stop();
            stopAccounts(as)
        }
}

## Account process handling credit requests issued by the teller, and debit
## requests issued by other accounts.
def account(self: AccountMb?, id: Int, balance: Int): Unit {
  guard self: (Debit + Credit)* . Stop {
    free ->
      ()
    receive Debit(accountMb, amount) from self ->

      accountMb ! Done();
      account(self, id, balance + amount)
    receive Credit(tellerMb, amount, accountMb) from self ->

      # A more uglier implementation would have been to use the 'global mailbox
      # way' where all messages are collected in one mailbox.
      let transMb = new [AccountMb] in
      accountMb ! Debit(transMb, amount);

      guard transMb: Done + 1{
        free ->
          account(self, id, balance)
        receive Done() from transMb ->
          free(transMb);
          tellerMb ! Reply();
          account(self, id, balance - amount)
      }

    receive Stop() from self ->
      account_exit(self)
  }
}

## Actor process exit procedure that flushes potential residual messages.
def account_exit(self: AccountMb?): Unit {
  guard self: (Debit + Credit)*  {
    free -> ()
    receive Debit(accountMb, amount) from self ->
      account_exit(self)
    receive Credit(tellerMb, amount, accountMb) from self ->
      account_exit(self)
  }
}

## Launcher.
def main(): Unit {
  let tellerMb = new [TellerMb] in
  spawn { teller(tellerMb, 3, (200 :: (150 :: (50 :: (nil : List(Int)))))) };

  tellerMb ! Start()
}

main()
