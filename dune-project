(lang dune 2.8)
(name pat)
(using menhir 2.1)

(generate_opam_files true)
(authors "Simon Fowler")
(maintainers "Simon Fowler")
(homepage "https://github.com/mailbox-types/pat-lang")
(bug_reports "https://github.com/mailbox-types/pat-lang")

(package
 (name pat)
 (synopsis "Typechecker and interpreter for the Pat programming language: the first programming language with support for mailbox types.")
 (depends
  (dune (>= 2.8))
  (ocaml (>= 5.2.0))
  cmdliner
  visitors
  ppx_import
  z3
  menhir
  bag
  eio
  eio_main
))
