(** Statistics over typed program environments. *)

open Annot

type interface_stats = {
  interface_name: string;
  name: string;
  npre: int;
  npost: int;
  nframe: int;
  ndeclaration_annotations: int;
}

type method_stats = {
  module_name: string;
  name: string;
  npre: int;
  npost: int;
  nframe: int;
  ndeclaration_annotations: int;
  nbody_annotations: int;
  ncommand_nodes: int;
  nassertions: int;
  ninvariants: int;
}

type bimethod_stats = {
  bimodule_name: string;
  name: string;
  npre: int;
  npost: int;
  nframe: int;
  ndeclaration_annotations: int;
  nbody_annotations: int;
  nunary_command_nodes: int;
  nrelational_command_nodes: int;
  nunary_assertions: int;
  nrelational_assertions: int;
  nunary_invariants: int;
  nrelational_invariants: int;
  nhavoc_right: int;
  nbilinks: int;
}

type stats = {
  interfaces: interface_stats list;
  methods: method_stats list;
  bimethods: bimethod_stats list;
  ninterface_auxiliaries: int;
  nmodule_auxiliaries: int;
  nbimodule_auxiliaries: int;
}

val measure : penv -> stats
val pp_stats : Format.formatter -> stats -> unit
val pp_stats_html : Format.formatter -> stats -> unit
val pp_stats_csv : Format.formatter -> stats -> unit
