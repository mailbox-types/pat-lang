# The Pat Programming Language

## About
This project is a typechecker and interpreter for the Pat programming language, introduced in the paper
[Special Delivery: Programming with Mailbox Types](https://dl.acm.org/doi/10.1145/3607832).

This paper extends the mailbox typing discipline
introduced by de' Liguoro and Padovani at ECOOP 2018
(https://drops.dagstuhl.de/opus/volltexte/2018/9220/pdf/LIPIcs-ECOOP-2018-15.pdf)
to the setting of a programming language.

## Credits

Several core ideas of our typechecking algorithm originated in the following, both by [Luca Padovani](https://boystrange.github.io/index.html):

  * [MCC](https://boystrange.github.io/mcc/)
  * [A type checking algorithm for concurrent object protocols](https://www.sciencedirect.com/science/article/pii/S2352220817301463)

## Installation

`Pat` is implemented in OCaml, a general-purpose functional programming language. OCaml can be installed by following these instructions.

### macOS

The easiest way to install OCaml on macOS is to use the Homebrew package manager. Homebrew can be downloaded and installed by following the instructions on the [website](https://brew.sh). Once Homebrew is installed and configured, the latest OCaml package manager, `opam`, can be installed as shown:

```bash
$ brew install opam
```

### Ubuntu

`opam` on Ubuntu Linux can be installed via the `apt` package manager.

```bash
$ sudo add-apt-repository ppa:avsm/ppa
$ sudo apt update
$ sudo apt install opam
```

On Ubuntu, one also needs to install `libgmp-dev`, which is a development library for the GMP (GNU Multiple Precision Arithmetic) that provides functions for performing arithmetic operations on large numbers. This library is used by the Z3 constraint solver invoked externally by the 'Pat' type checker.

```bash
sudo apt install libgmp-dev
```



### Initialising `opam`

The next step is to initialise `opam`:

```bash
$ opam init
```

Once the initialisation is completed, the following command updates the current shell environment.

```bash
$ eval $(opam env --switch=default)
```



## Downloading and building the `Pat`  type checker

`Pat` can be cloned from this GitHub repository as follows.

```bash
$ git clone https://github.com/SimonJF/pat.git
```

The `Pat` type checker uses a number of OCaml libraries that should be installed prior to compiling it.

```bash
$ opam install dune menhir ppx_import visitors cmdliner z3 bag
```

The type-checking tool can then be compiled using `make` after installing these dependencies.

```bash
$ cd pat
$ make
```


## Running

Usage: `./pat [options] <file>`. If the program completes successfully, then the
program typechecks and is interpreted by default.

### Arguments

`<file>`
: Path to the Pat source file to typecheck (required positional argument).

`-v`, `--verbose`
: Print verbose typechecking information.

`-d`, `--debug`
: Print debug information (including backtraces on internal errors).

`--ir`
: Print the translated intermediate representation (IR).

`--show-ref-counting`
: Run and print the IR after reference counting insertion.

`-t`, `--typecheck-only`
: Skip interpretation and perform typechecking only.

`--mode <MODE>`
: Choose typechecking mode for `receive` blocks. Allowed values:
  `strict`, `interface`, `none`.
  Default: `interface`.

`-b <BENCHMARK>`, `--benchmark <BENCHMARK>`
: Number of repetitions for benchmark runs.
  Use `-1` (default) to disable benchmarking.

`-q`, `--disable-quasilinearity`
: Disable quasilinearity checking.

`-j`, `--join-not-combine`
: Use sequential join for value subterms instead of requiring disjointness.

`-dt`, `--liberal-datatypes`
: Allow data contained in datatypes to be usable (may impact soundness).

### Example

```bash
./pat --mode strict --verbose test/examples/future.pat
```

Typecheck only (no interpreter):

```bash
./pat --typecheck-only test/examples/future.pat
```

## Mailbox Types

Mailbox types characterise communication with *mailboxes*: incoming message queues with
many writers and a single reader.

In short, mailbox types consist of a *capability* : either ! for output, similar
to a PID in Erlang, or ? for input; and a *pattern* which characterises the

A pattern is a *commutative regular expression* which denotes the pattern of
messages contained within that mailbox (for input capabilities), or the pattern
of messages which must be sent (for output capabilities).

There are various patterns:

  * 0: the unreliable mailbox (denotes an error)
  * 1: the empty mailbox
  * M: a message with tag M
  * E + F: either pattern E or pattern F
  * E . F: pattern E or F in any order
  * *E: many instances of pattern E

As a concrete example, the receive endpoint for an empty future can be given the
type

  ?(Put.*Get)

which states that the mailbox contains at most one Put message and many Get
messages; this would rule out the invalid behaviour of sending two Put messages.

## Base types

Pat also supports base types (String, Int, Bool) along with n-ary tuples and sum types.
User-defined algebraic datatypes are coming soon.

## Usable vs. Returnable Types

In order to avoid some horrible name hygiene issues, Pat uses *quasi-linear
typing*. In essence, this means that mailbox names can be used at most once in a
thread as a 'full' name (i.e., being allowed to be returned as part of an
expression, stored as part of a data type, etc.), and other times as a 'partial'
or 'second-class' name (allowing it to be used as part of an expression -- e.g.,
sending or passing as an argument).

Furthermore, the full or 'returnable' use must be the final lexical use of the
name.

Another point is that when receiving a mailbox name as part of a message, this
can only be treated as usable (and may not, therefore, escape the scope of the
`receive`).

These restrictions in turn rule out bad aliasing, use-after-free, and
self-deadlocks.

## Language Guide

Pat is a concurrent functional language with first-class mailboxes and mailbox
types. Examples can be found in the `examples` directory, but here we go over
some of the main points here.

### Interfaces

A message consists of a tag (i.e., a message name) and a list of message
payloads.

An *interface* describes the messages that a mailbox can receive.
Note that it does *not* describe any sequencing or pattern information about the
message. As an example, the interface for the `Future` example is as follows:

```
interface Future { Put(Int), Get(User!) }
interface User   { Reply(Int) }
```

Here, we can see that the `Future` interface says that a `Future` mailbox can
receive a `Put` message (with an `Int` payload), and a `Get` message (with a
`User!` payload), but it does not describe the invariant that the mailbox can
only contain a single Put message, for example. Interfaces are used to provide
type information for the inference pass.

### Programs

A Pat program consists of a series of *definitions* followed by a *body*.

Pat has very limited support for first-class functions, so instead a Pat program
typically consists of a series of *definitions*, which are explicitly annotated
with argument and return types, and contain an expression.
Definitions must be declared at the top level, and do not close over any values.

The body is a single expression, defined at the end of a file; a definition can
be called in the usual way.

Here is a simple Pat program:

```
def addTwoNumbers(x: Int, y: Int): Int {
  x + y
}

addTwoNumbers(10, 15)
```

This would have type Int.

### Basic Language Features

As a functional language, Pat has immutable data. Therefore, typically a Pat
expression consists of `let` bindings for intermediate computation steps:

```
  let x = 5 in
  let y = 10 in
  x + y
```

Variables `x` and `y` are standard.

Pat also includes side-effecting operations (such as sending messages), so we
also allow sequencing `e1; e2` where `e1` returns the unit value `()`.
The unit value is a value which conveys no information and is often used as a
return value for side-effecting operations.

### Concurrency Primitives

A mailbox is a message queue which can be written to by many processes, but read
by only one. In the actor model, a mailbox is associated with every process, and
messages are sent to that particular process ID.

#### Spawn

The `spawn M` construct spawns a term as a new process. Since the process will
run concurrently, all usages are masked as 2nd-class. For example, whereas the
following will not compile:

```
guard x : M { receive M() -> free(x) };
x ! M()
```

(since the first `guard` is returnable)

the following is permitted, since the `guard` is in a separate thread:

```
spawn { guard x : M { receive M() -> free(x) } };
x ! M()
```

#### Mailbox creation (new)

The mailbox calculus decouples *creation* of a mailbox from the process with
which it is associated. For this, we use the `new` construct:

`let mb = new[InterfaceName] in ...`

Here, `mb` will have type `?1`, denoting that all messages must have been
received.

#### Message send

To send a message to a mailbox, we use the `!` construct, which is similar to
Erlang.

`mb ! Foo(10)`

Here, we are sending a message with tag `Foo` and payload `10` to mailbox `mb`.
In this case, as a result of the send, `mb` will have type `!Foo`. By sending to
a mailbox reference, we create an obligation that the message must be received
by that mailbox.


#### Guards

Erlang has a `receive` statement to retrieve messages from a mailbox. The
analogous construct in Pat is `guard`, which is slightly generalised in that it
also allows us to free a mailbox that we know isn't being used.

As an example, here is a guard expression on a mailbox for a mailbox with type
`(M . N) + 1` (i.e., a mailbox which either has both `M` and `N` messages, or
does not contain any messages)

```
interface Test { M(Int), N(Int) }

let mb = new[Test] in
if (rand()) then {
  spawn { mb ! M(5) };
  spawn { mb ! N(10) }
} else {
  ()
};
in
guard mb : (M . N) + 1 {
  free -> ()
  receive M(x) from mb ->
    guard mb : N {
        receive N[y] from mb -> free(mb)
    }
  receive N(x) from mb ->
    guard mb : M {
        receive M[y] from mb -> free(mb)
    }
}
```

Note that in the `receive` clauses, the variable after `from` is a *binding*
occurrence.

Here, we specify the mailbox name we're guarding on (in this case, `mb`), along
with the pattern it currently contains (`(M . N) + 1`). We then add three guard
clauses:

  * `free` which handles the case where there are no messages in the mailbox,
      and the mailbox can be freed. Note that `mb` is not re-bound and so is
      unusable.

  * `receive M(x) from mb -> ...` which receives a message `M` from the mailbox,
      re-binding the mailbox name to `mb` with type `?N`

  * `receive N(x) from mb -> ...` which receives a message `N` from the mailbox,
      re-binding the mailbox name to `mb` with type `?M`

In both of the receive clauses, we need a further receive to clear the other
message.

We can also write `free(mb)` as syntactic sugar for the more verbose:

```
guard mb : 1 { free -> () }
```

## Overview of salient code locations
  * Lexer: `lib/frontend/lexer.mll`
  * Parser: `lib/frontend/parser.mly`
  * Desugaring: `lib/frontend/desugar_sugared_guards.ml` and
      `lib/frontend/insert_pattern_variables.ml`
  * IR conversion: `lib/frontend/sugar_to_ir.ml`
  * Constraint generation (backwards bidirectional typing):
      `lib/typecheck/gen_cosntraints.ml`
  * Constraint solving: `lib/typecheck/solve_constraints.ml` and
      `lib/typecheck/z3_solver.ml`
  * Examples: `test/examples`
  * Examples deliberately raising errors: `test/errors`
