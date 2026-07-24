# ICFP 2023 Artifact Instructions

Name: *Special Delivery: Programming with Mailbox Types*

## Artifact Instructions

This is the artifact for the paper "Special Delivery: Programming with Mailbox
Types". The artifact consists of a QEMU image (based on the ICFP base image)
containing the Pat typechecker and scripts to help evaluate the artifact.
The typechecker is written in OCaml, and uses Z3 as a backend solver for
Presburger formulae. Please see the "QEMU Instructions" section for instructions
on how to boot the QEMU image.

## Credentials

  * Username: artifact
  * Password: password

### Scope

The typechecker implements the bidirectional type system described in Section 4.
In addition, it implements all of the extensions (products, sums, lambdas, and
interfaces).  The artifact will also allow you to generate the table from the
Evaluation section of the paper; includes all of the examples from the paper and
evaluation; and will allow you to test your own examples.

### Sample evaluation workflow

  1. `cd pat` into the project directory.
  2. Build the `pat` binary by running `make`.
  2. Run the test suite by running `make test`.
  3. Try the examples from the paper (see the "Mapping to Paper" section)
  4. Generate the table from section 6 by running `./generate-table.py`. (Note,
     this is set to perform 100 iterations by default; you can change this by
     modifying the `REPETITIONS` parameter)
  5. Try your own examples, if you like! You can invoke the typechecker by
     `./pat <name>`. It will exit silently if the example typechecks. If you
     would like to see the inferred and simplified patterns, use the `-v` option.
  6. Have a look at the salient parts of the implementation (see the "Navigating
     the source code" section)

### Tool options

Invoke `pat` as `./pat <options> filename`. The options are as follows:
  * `-v`: verbose mode; outputs program with solved constraints
  * `-d`: debug mode; outputs detailed information about pattern constraints
  * `-b <count>` or `--benchmark=<count>`: output mean time taken to typecheck
      file over `<count>` iterations
  * `--ir` prints the IR after translation
  * `--mode=MODE` where `MODE` is one of `strict`, `interface`, or `none`:
      defines alias checking mode. `strict` requires that no free names occur
      within a guard; `interface` (default) requires that received names have a
      different interface to the free names in a guard; and `none` (unsound)
      turns off alias checking

### Mapping to Paper

All Pat code snippets in the paper, along with all examples, are included in the
artifact.

You can run all of these using the `./run-paper-examples.py` script.

  * The Future example from the introduction can be found in
      `test/examples/de_liguoro_padovani/future.pat`. This should typecheck without
      error.
  * The use-after-free examples should all raise errors, and can be found as follows:
    - Fig 3(a): `test/errors/uaf1.pat`
    - Fig 3(b): `test/errors/uaf2.pat`
    - Fig 3(c): `test/errors/uaf3.pat`
  * Programs introducing the problem in "Aliasing through communication" should
      also raise errors, and can be found in:
    - `test/errors/alias_comm1.pat`
    - `test/errors/alias_comm2.pat`
  * The product example from Sec 5.1 can be found in `test/examples/product.pat`
  * The interface example from Sec 5.1 can be found in `test/examples/interfaces.pat`
  * The de'Liguoro & Padovani examples from Sec 6 can be found in
      `test/examples/de_liguoro_padovani`.
  * The Savina examples from Sec 6 can be found in `test/examples/savina`.
  * The Robots case study from Sec 6 can be found in `test/examples/robotsn.pat`.

### Language guide & build / installation instructions
A guide to the language, as well as build and installation instructions, can be
found in `pat/README.md`.

### Difference between core calculus and concrete syntax

The implementation is fairly faithful to the syntax from Fig. 4, with the
following syntactic modifications:

  * Since we perform an A-normalisation step, it is possible to write nested
      expressions (i.e., `(1 + 2) + 3` rather than `let x = 1 + 2 in x + 3`).
  * It is not necessary to specify a pattern or usage when writing a mailbox
      type (you can see this, for example, in the Future example).
    - You can write `Future!` to mean a send mailbox with interface `Future`.
    - You can also ascribe a pattern to a mailbox type: for example, you could
        write `Future!Put` to denote a mailbox type with interface Future, which
        must send a Put message.
    - By default, send mailbox types are inferred as having a second-class
        usage, whereas receive mailbox types are inferred as being returnable.
        You can specify the usage explicitly using the `[U]` (for second-class)
        and `[R]` (for returnable) modifiers.
        So, to complete our example, a returnable output mailbox type for the Future
        interface which can send a Put message is `Future!Put[R]`
  * Messages are written with parentheses rather than braces (e.g., `x ! m(y)`
        rather than `x ! m[y]`).
  * We require interfaces as standard, so it's necessary to specify an interface
        name with `new`, i.e., `let x = new[Future] in ...`
  * Branches of case expressions are separated with a pipe (`|`) rather than a
      semicolon, i.e., `case V { inl x -> M | inr y -> N }`

### Navigating the source code

The source code can be found in the `pat` directory. Salient code locations
are as follows:

  * `bin/main.ml`: main entry point / command line processing
  * `lib/common/sugar_ast.ml`: post-parsing AST
  * `lib/common/ir.ml`: explicitly-sequenced intermediate representation
  * `lib/frontend/parser.mly`: grammar
  * `lib/frontend/pipeline.ml`: desugaring / typechecking pipeline
  * `lib/frontend/sugar_to_ir.ml`: IR conversion, converting sugared AST
      to explicitly-sequenced representation
  * `lib/typecheck/pretypecheck.ml`: contextual typing pass to propagate
      interface information (sec 5)
  * `lib/typecheck/gen_constraints.ml`: backwards bidirectional type system
      described in section 4
        - `synthesise_val` and `synthesise_comp` correspond to the synthesis
            judgement `M =P=> t |> env; constrs`
        - `check_val` and `check_comp` correspond to the checking judgement
            `M <=P= t |> env; constrs`
        - `check_guard` corresponds to the guard checking judgement
            `{E} G <=P= t |> Phi; consts; F`
  * `lib/typecheck/ty_env.ml`: algorithmic type & environment joining / merging
        - `combine` corresponds to disjoint combination `t1 + t2 |> t; constrs`
        - `join` corresponds to sequential combination `t1 ; t2 |> t; constrs`
        - `intersect` corresponds to disjoint combination `t1 cap t2 |> t; constrs`
  * `lib/typecheck/solve_constraints.ml` converts pattern constraints into
      Presburger formulae to be solved by Z3
  * `lib/typecheck/z3_solver.ml` interfaces with the Z3 solver

## QEMU Instructions

The ICFP 2023 Artifact Evaluation Process is using a Debian QEMU image as a
base for artifacts. The Artifact Evaluation Committee (AEC) will verify that
this image works on their own machines before distributing it to authors.
Authors are encouraged to extend the provided image instead of creating their
own. If it is not practical for authors to use the provided image then please
contact the AEC co-chairs before submission.

QEMU is a hosted virtual machine monitor that can emulate a host processor
via dynamic binary translation. On common host platforms QEMU can also use
a host provided virtualization layer, which is faster than dynamic binary
translation.

QEMU homepage: https://www.qemu.org/

### Installation

#### OSX
``brew install qemu``

#### Debian and Ubuntu Linux
``sudo apt update``
``sudo apt install qemu-system-x86``

On x86 laptops and server machines you may need to enable the
"Intel Virtualization Technology" setting in your BIOS, as some manufacturers
leave this disabled by default. See Debugging.md for details.


#### Arch Linux

``pacman -Sy qemu``

See the [Arch wiki](https://wiki.archlinux.org/title/QEMU) for more info.

See Debugging.md if you have problems logging into the artifact via SSH.


#### Windows 10

Download and install QEMU via the links at

https://www.qemu.org/download/#windows.

Ensure that `qemu-system-x86_64.exe` is in your path.

Start Bar -> Search -> "Windows Features"
          -> enable "Hyper-V" and "Windows Hypervisor Platform".

Restart your computer.

#### Windows 8

See Debugging.md for Windows 8 install instructions.

### Startup

The base artifact provides a `start.sh` script to start the VM on unix-like
systems and `start.bat` for Windows. Running this script will open a graphical
console on the host machine, and create a virtualized network interface.
On Linux you may need to run with `sudo` to start the VM. If the VM does not
start then check `Debugging.md`

Once the VM has started you can login to the guest system from the host.
Whenever you are asked for a password, the answer is `password`. The default
username is `artifact`.

```
$ ssh -p 5555 artifact@localhost
```

You can also copy files to and from the host using scp.

```
$ scp -P 5555 artifact@localhost:somefile .
```

### Shutdown

To shutdown the guest system cleanly, login to it via ssh and use

```
$ sudo shutdown now
```
