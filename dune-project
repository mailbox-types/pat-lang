(lang dune 2.8)
(name mbcheck)
(using menhir 2.1)

(generate_opam_files true)
(authors "Simon Fowler")
(maintainers "will add later")
(homepage "will add later")
(bug_reports "will add later")

(package
 (name mbcheck)
 (synopsis "Implementation of a typechecker for a programming language based on the mailbox calculus")
 (depends
  (dune (>= 2.8))
  (ocaml (>= 4.14.0))
  cmdliner
  visitors
  ppx_import
  z3
  menhir
  bag
  eio
  eio_main
))
