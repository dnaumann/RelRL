(** Statistics over typed program environments. *)

open Lib
open Astutil
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

let rec ncommand_nodes_of_command (c: command) : int =
  match c with
  | Acommand _ -> 1
  | Assume _ | Assert _ -> 0
  | Vardecl (_, _, _, c) | While (_, _, c) ->
    1 + ncommand_nodes_of_command c
  | Seq (c1, c2) | If (_, c1, c2) ->
    1 + ncommand_nodes_of_command c1 + ncommand_nodes_of_command c2

let num_option = function None -> 0 | Some _ -> 1

let rec nbody_annotations_of_command (c: command) : int =
  match c with
  | Assume _ | Assert _ -> 1
  | While (_, {winvariants; wvariant; wframe}, c) ->
    length winvariants + num_option wvariant + length wframe +
    nbody_annotations_of_command c
  | Vardecl (_, _, _, c) -> nbody_annotations_of_command c
  | Seq (c1, c2) | If (_, c1, c2) ->
    nbody_annotations_of_command c1 + nbody_annotations_of_command c2
  | Acommand _ -> 0

let rec nassertions_of_command (c: command) : int =
  match c with
  | Assume _ | Assert _ -> 1
  | Vardecl (_, _, _, c) -> nassertions_of_command c
  | Seq (c1, c2) | If (_, c1, c2) ->
    nassertions_of_command c1 + nassertions_of_command c2
  | While (_, _, c) -> nassertions_of_command c
  | _ -> 0

let rec ninvariants_of_command (c: command) : int =
  match c with
  | While (_, {winvariants=winv; _}, c) ->
    length winv + ninvariants_of_command c
  | Vardecl (_, _, _, c) -> ninvariants_of_command c
  | Seq (c1, c2) | If (_, c1, c2) ->
    ninvariants_of_command c1 + ninvariants_of_command c2
  | _ -> 0

let add_counts (u1, r1) (u2, r2) =
  map_pair (uncurry (+)) ((u1, u2), (r1, r2))

let rec ncommand_nodes_of_bicommand (cc: bicommand) : int * int =
  match cc with
  | Bisplit (c1, c2) ->
    (ncommand_nodes_of_command c1 + ncommand_nodes_of_command c2, 1)
  | Bivardecl (_, _, cc) | Biwhile (_, _, _, _, cc) ->
    add_counts (0, 1) (ncommand_nodes_of_bicommand cc)
  | Biseq (cc1, cc2) | Biif (_, _, cc1, cc2) ->
    add_counts (0, 1)
      (add_counts
         (ncommand_nodes_of_bicommand cc1)
         (ncommand_nodes_of_bicommand cc2))
  | Biif4 (_, _, {then_then; then_else; else_then; else_else}) ->
    add_counts (0, 1)
      (foldr add_counts (0, 0)
         (map ncommand_nodes_of_bicommand
            [then_then; then_else; else_then; else_else]))
  | Bihavoc_right _ | Bisync _ -> (0, 1)
  | Biassume _ | Biassert _ | Biupdate _ -> (0, 0)

let rec nbody_annotations_of_bicommand (cc: bicommand) : int =
  match cc with
  | Bihavoc_right _ | Biassume _ | Biassert _ | Biupdate _ -> 1
  | Bisplit (c1, c2) ->
    nbody_annotations_of_command c1 + nbody_annotations_of_command c2
  | Bivardecl (_, _, cc) -> nbody_annotations_of_bicommand cc
  | Biseq (cc1, cc2) | Biif (_, _, cc1, cc2) ->
    nbody_annotations_of_bicommand cc1 +
    nbody_annotations_of_bicommand cc2
  | Biif4 (_, _, {then_then; then_else; else_then; else_else}) ->
    foldr (+) 0 @@ map nbody_annotations_of_bicommand
      [then_then; then_else; else_then; else_else]
  | Biwhile (_, _, _, {biwinvariants; biwframe=(left, right);
                       biwvariant}, cc) ->
    length biwinvariants + length left + length right +
    num_option biwvariant + nbody_annotations_of_bicommand cc
  | Bisync _ -> 0

let rec nassertions_of_bicommand (cc: bicommand) : int * int =
  match cc with
  | Biassume _ | Biassert _ -> (0, 1)
  | Bisplit (c1, c2) ->
    (nassertions_of_command c1 + nassertions_of_command c2, 0)
  | Bivardecl (_, _, cc) | Biwhile (_, _, _, _, cc) ->
    nassertions_of_bicommand cc
  | Biseq (cc1, cc2) | Biif (_, _, cc1, cc2) ->
    add_counts
      (nassertions_of_bicommand cc1)
      (nassertions_of_bicommand cc2)
  | Biif4 (_, _, {then_then; then_else; else_then; else_else}) ->
    foldr add_counts (0, 0)
      (map nassertions_of_bicommand
         [then_then; then_else; else_then; else_else])
  | Bihavoc_right _ | Bisync _ | Biupdate _ -> (0, 0)

let rec ninvariants_of_bicommand (cc: bicommand) : int * int =
  match cc with
  | Bisplit (c1, c2) ->
    (ninvariants_of_command c1 + ninvariants_of_command c2, 0)
  | Bivardecl (_, _, cc) -> ninvariants_of_bicommand cc
  | Biseq (cc1, cc2) | Biif (_, _, cc1, cc2) ->
    add_counts
      (ninvariants_of_bicommand cc1)
      (ninvariants_of_bicommand cc2)
  | Biif4 (_, _, {then_then; then_else; else_then; else_else}) ->
    foldr add_counts (0, 0)
      (map ninvariants_of_bicommand
         [then_then; then_else; else_then; else_else])
  | Biwhile (_, _, _, {biwinvariants; _}, cc) ->
    add_counts (0, length biwinvariants) (ninvariants_of_bicommand cc)
  | Bihavoc_right _ | Bisync _ | Biassume _ | Biassert _ | Biupdate _ ->
    (0, 0)

let rec nhavoc_right_of_bicommand (cc: bicommand) : int =
  match cc with
  | Bihavoc_right _ -> 1
  | Bivardecl (_, _, cc) | Biwhile (_, _, _, _, cc) ->
    nhavoc_right_of_bicommand cc
  | Biseq (cc1, cc2) | Biif (_, _, cc1, cc2) ->
    nhavoc_right_of_bicommand cc1 + nhavoc_right_of_bicommand cc2
  | Biif4 (_, _, {then_then; then_else; else_then; else_else}) ->
    foldr (+) 0 @@ map nhavoc_right_of_bicommand
      [then_then; then_else; else_then; else_else]
  | Bisplit _ | Bisync _ | Biassume _ | Biassert _ | Biupdate _ -> 0

let rec nbilinks_of_bicommand (cc: bicommand) : int =
  match cc with
  | Biupdate _ -> 1
  | Bivardecl (_, _, cc) | Biwhile (_, _, _, _, cc) ->
    nbilinks_of_bicommand cc
  | Biseq (cc1, cc2) | Biif (_, _, cc1, cc2) ->
    nbilinks_of_bicommand cc1 + nbilinks_of_bicommand cc2
  | Biif4 (_, _, {then_then; then_else; else_then; else_else}) ->
    foldr (+) 0 @@ map nbilinks_of_bicommand
      [then_then; then_else; else_then; else_else]
  | Bihavoc_right _ | Bisplit _ | Bisync _ | Biassume _ | Biassert _ -> 0

let num_pre (s: spec) : int =
  length @@ filtermap (function Precond _ -> Some () | _ -> None) s

let num_post (s: spec) : int =
  length @@ filtermap (function Postcond _ -> Some () | _ -> None) s

let num_frame (s: spec) : int =
  foldr (+) 0 @@ filtermap (function
      | Effects effects -> Some (length effects)
      | _ -> None
    ) s

let num_bipre (s: bispec) : int =
  length @@ filtermap (function Biprecond _ -> Some () | _ -> None) s

let num_bipost (s: bispec) : int =
  length @@ filtermap (function Bipostcond _ -> Some () | _ -> None) s

let num_biframe (s: bispec) : int =
  foldr (+) 0 @@ filtermap (function
      | Bieffects (left, right) -> Some (length left + length right)
      | _ -> None
    ) s

let interface_stats_of_method (intr: string) (mdecl: meth_decl) =
  let npre = num_pre mdecl.meth_spec in
  let npost = num_post mdecl.meth_spec in
  let nframe = num_frame mdecl.meth_spec in
  { interface_name = intr;
    name = id_name mdecl.meth_name.node;
    npre;
    npost;
    nframe;
    ndeclaration_annotations = npre + npost + nframe;
  }

let method_stats_of_method (mdl: string) (m: meth_def) =
  let Method (mdecl, com) = m in
  let npre = num_pre mdecl.meth_spec in
  let npost = num_post mdecl.meth_spec in
  let nframe = num_frame mdecl.meth_spec in
  let ncommand_nodes, nassertions, ninvariants = match com with
    | Some c ->
      (ncommand_nodes_of_command c, nassertions_of_command c,
       ninvariants_of_command c)
    | None -> (0, 0, 0) in
  let nbody_annotations = match com with
    | Some c -> nbody_annotations_of_command c
    | None -> 0 in
  { module_name = mdl;
    name = id_name mdecl.meth_name.node;
    npre;
    npost;
    nframe;
    ndeclaration_annotations = npre + npost + nframe;
    nbody_annotations;
    ncommand_nodes;
    nassertions;
    ninvariants;
  }

let bimethod_stats_of_bimethod (bimdl: string) (bm: bimeth_def) =
  let Bimethod (bmdecl, bicom) = bm in
  let npre = num_bipre bmdecl.bimeth_spec in
  let npost = num_bipost bmdecl.bimeth_spec in
  let nframe = num_biframe bmdecl.bimeth_spec in
  let nunary_command_nodes, nrelational_command_nodes = match bicom with
    | Some cc -> ncommand_nodes_of_bicommand cc
    | None -> (0, 0) in
  let nunary_assertions, nrelational_assertions = match bicom with
    | Some cc -> nassertions_of_bicommand cc
    | None -> (0, 0) in
  let nunary_invariants, nrelational_invariants = match bicom with
    | Some cc -> ninvariants_of_bicommand cc
    | None -> (0, 0) in
  let nhavoc_right = match bicom with
    | Some cc -> nhavoc_right_of_bicommand cc
    | None -> 0 in
  let nbilinks = match bicom with
    | Some cc -> nbilinks_of_bicommand cc
    | None -> 0 in
  let nbody_annotations = match bicom with
    | Some cc -> nbody_annotations_of_bicommand cc
    | None -> 0 in
  { bimodule_name = bimdl;
    name = id_name bmdecl.bimeth_name;
    npre;
    npost;
    nframe;
    ndeclaration_annotations = npre + npost + nframe;
    nbody_annotations;
    nunary_command_nodes;
    nrelational_command_nodes;
    nunary_assertions;
    nrelational_assertions;
    nunary_invariants;
    nrelational_invariants;
    nhavoc_right;
    nbilinks;
  }

let ninterface_auxiliaries intr =
  length @@ filtermap (function
      | Intr_formula _ | Intr_inductive _ -> Some ()
      | _ -> None
    ) intr.intr_elts

let nmodule_auxiliaries mdl =
  length @@ filtermap (function
      | Mdl_formula _ | Mdl_inductive _ -> Some ()
      | _ -> None
    ) mdl.mdl_elts

let nbimodule_auxiliaries bimdl =
  length @@ filtermap (function
      | Bimdl_formula _ -> Some ()
      | _ -> None
    ) bimdl.bimdl_elts

let measure penv =
  let measure_program_elt _ program stats =
    match program with
    | Unary_interface intr ->
      let add_method elt interfaces = match elt with
        | Intr_mdecl mdecl ->
          interface_stats_of_method (id_name intr.intr_name) mdecl ::
          interfaces
        | _ -> interfaces in
      {stats with
       interfaces = foldl add_method stats.interfaces intr.intr_elts;
       ninterface_auxiliaries =
         stats.ninterface_auxiliaries + ninterface_auxiliaries intr}
    | Unary_module mdl ->
      let add_method elt methods = match elt with
        | Mdl_mdef mdef ->
          method_stats_of_method (id_name mdl.mdl_name) mdef :: methods
        | _ -> methods in
      {stats with
       methods = foldl add_method stats.methods mdl.mdl_elts;
       nmodule_auxiliaries =
         stats.nmodule_auxiliaries + nmodule_auxiliaries mdl}
    | Relation_module bimdl ->
      let add_bimethod elt bimethods = match elt with
        | Bimdl_mdef bmdef ->
          bimethod_stats_of_bimethod (id_name bimdl.bimdl_name) bmdef ::
          bimethods
        | _ -> bimethods in
      {stats with
       bimethods = foldl add_bimethod stats.bimethods bimdl.bimdl_elts;
       nbimodule_auxiliaries =
         stats.nbimodule_auxiliaries + nbimodule_auxiliaries bimdl}
  in
  let empty = {
    interfaces=[];
    methods=[];
    bimethods=[];
    ninterface_auxiliaries=0;
    nmodule_auxiliaries=0;
    nbimodule_auxiliaries=0;
  } in
  let stats = M.fold measure_program_elt penv empty in
  {stats with
   interfaces = rev stats.interfaces;
   methods = rev stats.methods;
   bimethods = rev stats.bimethods}

let interface_rows interfaces =
  map (fun
      {interface_name; name; npre; npost; nframe;
       ndeclaration_annotations} ->
      [interface_name; name; string_of_int npre; string_of_int npost;
       string_of_int nframe; string_of_int ndeclaration_annotations]
    ) interfaces

let method_rows methods =
  map (fun
      {module_name; name; npre; npost; nframe; ncommand_nodes;
       ndeclaration_annotations; nbody_annotations;
       nassertions; ninvariants} ->
      [module_name; name; string_of_int npre; string_of_int npost;
       string_of_int nframe; string_of_int ndeclaration_annotations;
       string_of_int nbody_annotations; string_of_int ncommand_nodes;
       string_of_int nassertions;
       string_of_int ninvariants]
    ) methods

let bimethod_rows bimethods =
  map (fun
      {bimodule_name; name; npre; npost; nframe;
       ndeclaration_annotations; nbody_annotations;
       nunary_command_nodes; nrelational_command_nodes;
       nunary_assertions; nrelational_assertions;
       nunary_invariants; nrelational_invariants; nhavoc_right; nbilinks} ->
      [bimodule_name; name; string_of_int npre; string_of_int npost;
       string_of_int nframe; string_of_int ndeclaration_annotations;
       string_of_int nbody_annotations;
       string_of_int nunary_command_nodes;
       string_of_int nrelational_command_nodes;
       string_of_int nunary_assertions;
       string_of_int nrelational_assertions;
       string_of_int nunary_invariants;
       string_of_int nrelational_invariants; string_of_int nhavoc_right;
       string_of_int nbilinks]
    ) bimethods

let auxiliary_rows ninterface nmodule nbimodule =
  let total = ninterface + nmodule + nbimodule in
  [["Interfaces"; string_of_int ninterface];
   ["Unary modules"; string_of_int nmodule];
   ["Relational modules"; string_of_int nbimodule];
   ["Total"; string_of_int total]]

let update_widths cells widths =
  let rec update cells widths =
    match cells, widths with
    | [], [] -> []
    | cell :: cells, [] ->
      String.length cell :: update cells []
    | cell :: cells, width :: widths ->
      max (String.length cell) width :: update cells widths
    | [], _ :: _ -> widths
  in update cells widths

let table_border widths =
  "+" ^ foldr (fun width rest ->
      String.make (width + 2) '-' ^ "+" ^ rest
    ) "" widths

let pp_table_row widths outf cells =
  let rec pp widths cells =
    match widths, cells with
    | [], [] -> Format.fprintf outf "|"
    | width :: widths, cell :: cells ->
      let padding = String.make (width - String.length cell) ' ' in
      Format.fprintf outf "| %s%s " cell padding;
      pp widths cells
    | _ -> invalid_arg "pp_table_row"
  in pp widths cells

let pp_table outf title headers rows =
  let widths = foldl update_widths [] (headers :: rows) in
  let border = table_border widths in
  Format.fprintf outf "%s@.%s@.%a@.%s@."
    title border (pp_table_row widths) headers border;
  let pp_row row () =
    Format.fprintf outf "%a@." (pp_table_row widths) row in
  ignore (foldl pp_row () rows);
  Format.fprintf outf "%s" border

let interface_headers =
  ["Interface"; "Method"; "Pre"; "Post"; "Frame"; "Declaration annotations"]

let method_headers =
  ["Module"; "Method"; "Pre"; "Post"; "Frame";
   "Declaration annotations"; "Body annotations";
   "Command nodes"; "Assertions/assumptions"; "Invariants"]

let bimethod_headers =
  ["Bimodule"; "Method"; "Pre"; "Post"; "Frame";
   "Declaration annotations"; "Body annotations";
   "Unary command nodes"; "Rel. command nodes";
   "Unary asserts/assumes"; "Rel. asserts/assumes";
   "Unary invariants"; "Rel. invariants"; "HavocR"; "BiLinks"]

let auxiliary_headers = ["Owner kind"; "Definitions"]

let pp_stats outf
    {interfaces; methods; bimethods;
     ninterface_auxiliaries; nmodule_auxiliaries; nbimodule_auxiliaries} =
  Format.fprintf outf "@[<v>%a@.@.%a@.@.%a@.@.%a@]"
    (fun outf () ->
       pp_table outf "Interface methods" interface_headers
         (interface_rows interfaces)) ()
    (fun outf () ->
       pp_table outf "Unary methods" method_headers (method_rows methods)) ()
    (fun outf () ->
       pp_table outf "Relational methods" bimethod_headers
         (bimethod_rows bimethods)) ()
    (fun outf () ->
       pp_table outf "Auxiliary definitions" auxiliary_headers
         (auxiliary_rows ninterface_auxiliaries nmodule_auxiliaries
            nbimodule_auxiliaries)) ()

let html_escape s =
  let escaped = Buffer.create (String.length s) in
  String.iter (function
      | '&' -> Buffer.add_string escaped "&amp;"
      | '<' -> Buffer.add_string escaped "&lt;"
      | '>' -> Buffer.add_string escaped "&gt;"
      | '"' -> Buffer.add_string escaped "&quot;"
      | '\'' -> Buffer.add_string escaped "&#39;"
      | c -> Buffer.add_char escaped c
    ) s;
  Buffer.contents escaped

let pp_html_cells tag outf cells =
  let pp_cell cell () =
    Format.fprintf outf "<%s>%s</%s>" tag (html_escape cell) tag in
  ignore (foldl pp_cell () cells)

let pp_html_table outf title headers rows =
  Format.fprintf outf
    "<div class=\"section\"><h2>%s</h2><div class=\"table-wrap\"><table>\
     <thead><tr>%a</tr>\
     </thead><tbody>"
    (html_escape title) (pp_html_cells "th") headers;
  let pp_row row () =
    Format.fprintf outf "<tr>%a</tr>" (pp_html_cells "td") row in
  ignore (foldl pp_row () rows);
  Format.fprintf outf "</tbody></table></div></div>"

let pp_stats_html outf
    {interfaces; methods; bimethods;
     ninterface_auxiliaries; nmodule_auxiliaries; nbimodule_auxiliaries} =
  Format.fprintf outf
    "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\
     <meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">\
     <title>WhyRel statistics</title><style>\
     :root{color-scheme:light dark;font-family:system-ui,sans-serif}\
     body{margin:0;padding:32px;background:#f5f6f7;color:#181a1b}\
     .main{max-width:1440px;margin:auto}h1{font-size:24px;margin:0 0 24px}\
     h2{font-size:16px;margin:24px 0 8px}.table-wrap{overflow-x:auto}\
     table{border-collapse:collapse;width:100%%;background:#fff}\
     th,td{border:1px solid #c9ced3;padding:7px 9px;text-align:left;\
     white-space:nowrap}th{background:#e9edf0;font-weight:600}\
     tbody tr:nth-child(even){background:#f7f8f9}\
     @@media(prefers-color-scheme:dark){body{background:#151718;color:#eee}\
     table{background:#202325}th{background:#303438}th,td{border-color:#555}\
     tbody tr:nth-child(even){background:#272a2d}}</style></head>\
     <body><div class=\"main\"><h1>WhyRel statistics</h1>%a%a%a%a\
     </div></body></html>"
    (fun outf () ->
       pp_html_table outf "Interface methods" interface_headers
         (interface_rows interfaces)) ()
    (fun outf () ->
       pp_html_table outf "Unary methods" method_headers
         (method_rows methods)) ()
    (fun outf () ->
       pp_html_table outf "Relational methods" bimethod_headers
         (bimethod_rows bimethods)) ()
    (fun outf () ->
       pp_html_table outf "Auxiliary definitions" auxiliary_headers
         (auxiliary_rows ninterface_auxiliaries nmodule_auxiliaries
            nbimodule_auxiliaries)) ()

let csv_headers =
["Kind"; "Owner"; "Method"; "Preconditions"; "Postconditions";
 "Frame effects"; "Declaration annotations"; "Body annotations";
 "Command nodes"; "Assertions/assumptions"; "Invariants";
 "Unary command nodes"; "Relational command nodes";
 "Unary assertions/assumptions"; "Relational assertions/assumptions";
 "Unary invariants"; "Relational invariants"; "HavocR";
 "BiLinks"; "Auxiliary definitions"]

let csv_interface_rows interfaces =
map (fun
    {interface_name; name; npre; npost; nframe;
     ndeclaration_annotations} ->
    ["Interface"; interface_name; name; string_of_int npre;
     string_of_int npost; string_of_int nframe;
     string_of_int ndeclaration_annotations; "0"] @ replicate 12 ""
  ) interfaces

let csv_method_rows methods =
map (fun
    {module_name; name; npre; npost; nframe; ncommand_nodes;
     ndeclaration_annotations; nbody_annotations;
     nassertions; ninvariants} ->
    ["Unary method"; module_name; name; string_of_int npre;
     string_of_int npost; string_of_int nframe;
     string_of_int ndeclaration_annotations;
     string_of_int nbody_annotations;
     string_of_int ncommand_nodes; string_of_int nassertions;
     string_of_int ninvariants] @ replicate 9 ""
  ) methods

let csv_bimethod_rows bimethods =
map (fun
    {bimodule_name; name; npre; npost; nframe;
     ndeclaration_annotations; nbody_annotations;
     nunary_command_nodes; nrelational_command_nodes;
     nunary_assertions; nrelational_assertions;
     nunary_invariants; nrelational_invariants; nhavoc_right; nbilinks} ->
    ["Relational method"; bimodule_name; name; string_of_int npre;
     string_of_int npost; string_of_int nframe;
     string_of_int ndeclaration_annotations;
     string_of_int nbody_annotations; ""; ""; "";
     string_of_int nunary_command_nodes;
     string_of_int nrelational_command_nodes;
     string_of_int nunary_assertions; string_of_int nrelational_assertions;
     string_of_int nunary_invariants; string_of_int nrelational_invariants;
     string_of_int nhavoc_right; string_of_int nbilinks; ""]
  ) bimethods

let csv_auxiliary_rows ninterface nmodule nbimodule =
map (fun (owner, count) ->
    ["Auxiliary"; owner] @ replicate 17 "" @ [string_of_int count]
  )
  [("Interfaces", ninterface);
   ("Unary modules", nmodule);
   ("Relational modules", nbimodule);
   ("Total", ninterface + nmodule + nbimodule)]

let csv_escape value =
let escaped = Buffer.create (String.length value + 2) in
Buffer.add_char escaped '"';
String.iter (fun c ->
    if c = '"' then Buffer.add_string escaped "\"\""
    else Buffer.add_char escaped c
  ) value;
Buffer.add_char escaped '"';
Buffer.contents escaped

let pp_csv_row outf cells =
let rec pp = function
  | [] -> Format.fprintf outf "\r\n"
  | [cell] -> Format.fprintf outf "%s\r\n" (csv_escape cell)
  | cell :: cells ->
    Format.fprintf outf "%s," (csv_escape cell);
    pp cells
in pp cells

let pp_stats_csv outf
  {interfaces; methods; bimethods;
   ninterface_auxiliaries; nmodule_auxiliaries; nbimodule_auxiliaries} =
let rows =
  csv_interface_rows interfaces @
  csv_method_rows methods @
  csv_bimethod_rows bimethods @
  csv_auxiliary_rows ninterface_auxiliaries nmodule_auxiliaries
    nbimodule_auxiliaries in
pp_csv_row outf csv_headers;
ignore (foldl (fun row () -> pp_csv_row outf row) () rows)
