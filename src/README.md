# Inventory

./tools

  main.ml - entry point to WhyRel

./util

  lib.ml - a small library of utility functions
  why3util.ml - functions to construct Why3 parse trees

./parser

  ast.ml - abstract syntax of the object language
  astutil.ml - utility functions on syntax
  lexer.mll - lexer
  parser.mly - parser (Menhir)

./typing

  annot.ml - type annotated syntax trees + utility functions
  ctbl.{ml,mli} - class tables
  pretty.ml - rudimentary pretty printer for WhyRel syntax trees
  typing.ml - type checking and well-formedness conditions

./pretrans

  boundary_info.{ml,mli} - cache information about module boundaries
  derive_biinterface.ml - construct interfaces for bimodules
  encap_check.{ml,mli} - encapsulation check
  locEq.{ml,mli} - derive local equivalence specs
  pretrans.ml - performs various analyses + adds proof obligations
  resolve_datagroups.{ml,mli} - expand uses of datagroup `any`

./translate

  translate.ml - translate annotated syntax trees to Why3 parse trees
  why3constants.ml - names for Why3 constants
