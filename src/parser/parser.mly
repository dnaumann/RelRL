%{

open Ast

let loc_of_lexing_positions (l1, l2) =
  let open Lexing in
  let loc_fname = l1.pos_fname in
  let loc_line = l1.pos_lnum in
  let start_pt = l1.pos_cnum - l1.pos_bol in
  let end_pt = l2.pos_cnum - l1.pos_bol in
  {loc_fname; loc_line; loc_range = (start_pt,end_pt) }

let mk_node (e: 'a) (l1, l2) =
  { elt = e; loc = loc_of_lexing_positions (l1, l2) }

let mk_qbind x t rgn loc =
  let ty, is_non_null =
    match t with
    | `Can_be_null t -> (t, false)
    | `Non_null t -> (t, true) in
  { name = x;
    ty = ty;
    in_rgn = rgn;
    is_non_null = is_non_null
  }

let mk_meth_param_info modifier name t =
  let pty, is_non_null =
    match t with
    | `Can_be_null t -> (t, false)
    | `Non_null t -> (t, true) in
  { param_name = name;
    param_modifier = modifier;
    param_ty = pty;
    is_non_null = is_non_null
  }

let mk_meth_decl mname params rty spec =
  let rty, is_non_null =
    match rty with
    | `Can_be_null t -> (t, false)
    | `Non_null t -> (t, true) in
  { meth_name = mname;
    params = params;
    result_ty = rty;
    result_is_non_null = is_non_null;
    meth_spec = spec;
  }

let mk_bimeth_decl mname params_left params_right ret_left ret_right bispec =
  let is_non_null = function
    | `Can_be_null _ -> false
    | `Non_null _ -> true in
  let get_ty = function
    | `Can_be_null t | `Non_null t -> t in
  let left_null_status, right_null_status =
    is_non_null ret_left, is_non_null ret_right in
  { bimeth_name = mname;
    bimeth_left_params = params_left;
    bimeth_right_params = params_right;
    result_ty = (get_ty ret_left, get_ty ret_right);
    result_is_non_null = (left_null_status, right_null_status);
    bimeth_spec = bispec;
  }

let mk_extern_symbol sym kind inp biinp out def =
  { extern_symbol = sym;
    extern_kind = kind;
    extern_input = inp;
    extern_biinput = biinp;
    extern_output = out;
    extern_default = def;
  }

let mk_effect_elt kind desc loc =
  let mk kind desc = mk_node {effect_kind = kind; effect_desc = desc} loc in
  let mk_effect_desc = function
    | `Ident id -> Effvar id
    | `Image (g,f) -> Effimg (g,f) in
  let desc = mk_effect_desc desc in
  match kind with
  | `Read_effect -> [mk Read desc]
  | `Write_effect -> [mk Write desc]
  | `Readwrite_effect -> [mk Read desc; mk Write desc]

let mk_boundary_elt loc desc =
  let open Lexing in
  match desc.elt with
  | `Ident id -> mk_node (Effvar id) loc
  | `Image (g,f) -> mk_node (Effimg (g,f)) loc

%}

%token EOF

%token GHOST                    /* ghost */
%token PUBLIC                   /* public */
%token PRIVATE                  /* private */
%token COUPLING                 /* coupling */
%token MODSCOPE                 /* modscope */

%token <string> UIDENT          /* upper case identifier */
%token <string> LIDENT          /* lower case identifier */

%token PLUS                     /* + */
%token MINUS                    /* - */
%token MULT                     /* * */
%token DIV                      /* / */
%token MOD                      /* mod */
%token UNION                    /* union */
%token INTER                    /* inter */
%token DIFF                     /* diff */
%token IN                       /* in */
%token NOTIN                    /* notin */
%token SUBSETEQ                 /* subset */
%token DISJOINT                 /* # */
%token IMAGE                    /* ` */
%token SUBRGN                   /* of */
%token NOT                      /* not */
%token AND                      /* and */
%token OR                       /* or */
%token EQUAL                    /* = */
%token NOTEQUAL                 /* != */
%token LEQ                      /* <= */
%token LT                       /* < */
%token GT                       /* > */
%token GEQ                      /* >= */

%token NULL                     /* null */
%token MAYBE_NULL               /* ? */
%token TRUE                     /* true */
%token FALSE                    /* false */
%token <int> INT                /* <integer> */

%token FRM_TRUE                 /* True */
%token FRM_FALSE                /* False */
%token FRM_NOT                  /* ~ */
%token FRM_TYPE                 /* Type */
%token CONJ                     /* /\ */
%token DISJ                     /* \/ */
%token IMP                      /* => */
%token IFF                      /* <=> */
%token LET                      /* let */
%token OLD                      /* old */
%token INIT                     /* init */
%token FORALL                   /* forall */
%token EXISTS                   /* exists */

%token SKIP                     /* skip */
%token ASSIGN                   /* := */
%token HAVOC                    /* havoc */
%token NEW                      /* new */
%token VAR                      /* var */
%token IF                       /* if */
%token THEN                     /* then */
%token ELSE                     /* else */
%token WHILE                    /* while */
%token DO                       /* do */
%token INVARIANT                /* invariant */
%token VARIANT                  /* variant */
%token DONE                     /* done */
%token ASSUME                   /* assume */
%token ASSERT                   /* assert */

%token READ                     /* rd */
%token WRITE                    /* wr */
%token READWRITE                /* rw */
%token REQUIRES                 /* requires */
%token ENSURES                  /* ensures */
%token EFFECTS                  /* effects */
%token EFFECT_RDS               /* reads */
%token EFFECT_WRS               /* writes */
%token EFFECT_RWS               /* reads/writes */

%token METH                     /* meth */
%token CLASS                    /* class */
%token INTERFACE                /* interface */
%token END                      /* end */

%token PREDICATE                /* predicate */
%token INDUCTIVE                /* inductive */
%token BIPREDICATE              /* bipredicate */
%token AXIOM                    /* axiom */
%token LEMMA                    /* lemma */

%token IMPORT                   /* import */
%token THEORY                   /* theory */
%token AS                       /* as */
%token BOUNDARY                 /* boundary */
%token DATAGROUP                /* datagroup */
%token CONTAINS                 /* contains */

%token MODULE                   /* module */
%token BIMODULE                 /* bimodule */

%token LPAREN                   /* ( */
%token RPAREN                   /* ) */
%token LBRACE                   /* { */
%token RBRACE                   /* } */
%token LBRACK                   /* [ */
%token RBRACK                   /* ] */
%token COMMA                    /* , */
%token COLON                    /* : */
%token SEMICOLON                /* ; */
%token DOT                      /* . */

%token BAR                      /* | */
%token LEFT_OPEN                /* <| */
%token LEFT_EXP_OPEN            /* [< */
%token LEFT_CLOSE               /* <] */
%token RIGHT_OPEN               /* [> */
%token RIGHT_EXP_CLOSE          /* >] */
%token RIGHT_CLOSE              /* |> */

%token BIEQUAL                  /* =:= */
%token LEFT_SYNC                /* |_ */
%token RIGHT_SYNC               /* _| */
%token AGREE                    /* Agree */
%token BOTH                     /* Both */

%token PUBLIC_INV_ANNOT         /* public */
%token PRIVATE_INV_ANNOT        /* private */
%token COUPLING_ANNOT           /* coupling */

%token BIHAVOC                  /* HavocR */
%token BIVAR                    /* Var */
%token BIIF                     /* If */
%token BIWHILE                  /* While */
%token BIWHILELEFT              /* WhileL */
%token BIWHILERIGHT             /* WhileR */
%token BIASSUME                 /* Assume */
%token BIASSERT                 /* Assert */
%token BIUPDATE                 /* Link */
%token WITH                     /* With */

%token BIIFFOUR                 /* If4 */
%token BITHENTHEN               /* then@then */
%token BITHENELSE               /* then@else */
%token BIELSETHEN               /* else@then */
%token BIELSEELSE               /* else@else */

%token EXTERN                   /* extern */
%token TYPE                     /* type */
%token CONST                    /* const */
%token DEFAULT                  /* default */

%token RELATED                  /* related */
%token BY                       /* by */
%token MAIN_MODULE              /* Main */

%right IN
%nonassoc BAR
%right SEMICOLON
%right IMP
%nonassoc IFF
%right OR DISJ
%right AND CONJ
%nonassoc LEQ LT GEQ GT
%right NOTEQUAL EQUAL
%left MOD
%left PLUS MINUS
%left MULT DIV
%right SUBRGN
%left UNION INTER DIFF
%left IMAGE
%nonassoc BOTH
%nonassoc UMINUS

%start <Ast.program> top

%%

top:
  | i=program EOF { i }
  ;

simple_lident:
  | id=LIDENT { Id id }
  ;

simple_uident:
  | id=UIDENT { Id id }
  ;

ident:
  | id=simple_uident { id }
  | id=simple_lident { id }
  ;

ty:
  | t=option(ty); id=ident
    { mk_node
    begin match t with
    | None -> Tctor(id, [])
    | Some t -> Tctor(id, [t])
    end
      $loc
    }
  | LPAREN; t=ty; RPAREN
    { t }
  ;

%inline const_exp:
  | NULL                { mk_node Enull $loc }
  | LPAREN; RPAREN      { mk_node Eunit $loc }
  | TRUE                { mk_node (Ebool true) $loc }
  | FALSE               { mk_node (Ebool false) $loc }
  | i=INT               { mk_node (Eint i) $loc }
  | LBRACE; RBRACE      { mk_node Eemptyset $loc }
  ;

exp:
  | c=const_exp { mk_node (Econst c) $loc }
  | id=ident { mk_node (Evar id) $loc }
  | LBRACE; e=exp; RBRACE { mk_node (Esingleton e) $loc }
  | e1=exp; op=binop; e2=exp { mk_node (Ebinop(op,e1,e2)) $loc }
  | k=ident; SUBRGN; e=exp { mk_node (Esubrgn(e,k)) $loc }
  | MINUS; e=exp %prec UMINUS { mk_node (Eunrop(Uminus,e)) $loc }
  | NOT; e=exp %prec UMINUS { mk_node (Eunrop(Not,e)) $loc }
  | g=exp; IMAGE; f=ident { mk_node (Eimage(g,f)) $loc }
  | fn=ident; LPAREN; args=separated_list(COMMA,exp); RPAREN
    { mk_node (Ecall(fn,args)) $loc }
  | LPAREN; e=exp; RPAREN { e }
  ;

%inline binop:
  | PLUS        { Plus }
  | MINUS       { Minus }
  | MULT        { Mult }
  | DIV         { Div }
  | UNION       { Union }
  | INTER       { Inter }
  | DIFF        { Diff }
  | AND         { And }
  | OR          { Or }
  | EQUAL       { Equal }
  | NOTEQUAL    { Nequal }
  | LEQ         { Leq }
  | LT          { Lt }
  | GEQ         { Geq }
  | GT          { Gt }
  | MOD         { Mod }
  ;

formula:
  | f=formula1 { f }
  | e=exp { mk_node (Fexp e) $loc }
  ;

formula1:
  | FRM_TRUE { mk_node Ftrue $loc }
  | FRM_FALSE { mk_node Ffalse $loc }
  | f=pointsto_formula { f }
  | f=array_pointsto_formula { f }
  | e1=exp; SUBSETEQ; e2=exp { mk_node (Fsubseteq(e1,e2)) $loc }
  | e1=exp; DISJOINT; e2=exp { mk_node (Fdisjoint(e1,e2)) $loc }
  | e1=exp; IN; e2=exp { mk_node (Fmember(e1,e2)) $loc }
  | e1=exp; NOTIN; e2=exp
    { let inner = mk_node (Fmember(e1,e2)) $loc in
      mk_node (Fnot inner) $loc }
  | f1=formula; c=connective; f2=formula { mk_node (Fconn(c,f1,f2)) $loc }
  | FRM_NOT; f=formula %prec UMINUS { mk_node (Fnot f) $loc }
  | INIT; LPAREN; e=let_bound_value; RPAREN { mk_node (Finit e) $loc }
  | f=let_formula { f }
  | f=quantified_formula %prec IN { f }
  | LPAREN; f=formula1; RPAREN { f }
  | x=exp; EQUAL; OLD; LPAREN; valu=let_bound_value; RPAREN
    { mk_node (Fold(x,valu)) $loc }
  | FRM_TYPE; LPAREN; e=exp; COMMA; tys=separated_nonempty_list(BAR,ident); RPAREN
    { mk_node (Ftype(e,tys)) $loc }
  ;

pointsto_formula:
  | x=ident; DOT; f=ident; EQUAL; e=exp
    { mk_node (Fpointsto(x,f,e)) $loc }
  | e=exp; EQUAL; x=ident; DOT; f=ident
    { mk_node (Fpointsto(x,f,e)) $loc }
  | x=ident; DOT; f=ident; NOTEQUAL; e=exp
    { let inner = mk_node (Fpointsto(x,f,e)) $loc in
      mk_node (Fnot inner) $loc }
  | e=exp; NOTEQUAL; x=ident; DOT; f=ident
    { let inner = mk_node (Fpointsto(x,f,e)) $loc in
      mk_node (Fnot inner) $loc }
  ;

array_pointsto_formula:
  | a=ident; LBRACK; idx=exp; RBRACK; EQUAL; e=exp
    { mk_node (Farray_pointsto(a,idx,e)) $loc }
  | e=exp; EQUAL; a=ident; LBRACK; idx=exp; RBRACK
    { mk_node (Farray_pointsto(a,idx,e)) $loc }
  | a=ident; LBRACK; idx=exp; RBRACK; NOTEQUAL; e=exp
    { let inner = mk_node (Farray_pointsto(a,idx,e)) $loc in
      mk_node (Fnot inner) $loc }
  | e=exp; NOTEQUAL; a=ident; LBRACK; idx=exp; RBRACK
    { let inner = mk_node (Farray_pointsto(a,idx,e)) $loc in
      mk_node (Fnot inner) $loc }
  ;

let_formula:
  | LET; x=simple_lident; t=option(preceded(COLON, ty)); EQUAL; u=let_bound_value;
    IN; frm=formula
    { mk_node (Flet(x, t, { value = u; is_old = false; is_init = false }, frm)) $loc }
  | LET; x=simple_lident; t=option(preceded(COLON, ty)); EQUAL;
    OLD; LPAREN; u=let_bound_value; RPAREN; IN; frm=formula
    { mk_node (Flet(x, t, { value = u; is_old = true; is_init = false }, frm)) $loc }
  | LET; x=simple_lident; t=option(preceded(COLON, ty)); EQUAL;
    INIT; LPAREN; u=let_bound_value; RPAREN; IN; frm=formula
    { mk_node (Flet(x, t, { value = u; is_old = false; is_init = true }, frm)) $loc }
  ;

%inline let_bound_value:
  | y=ident; DOT; fld=ident           { mk_node (Lloc(y,fld)) $loc }
  | e=exp                             { mk_node (Lexp(e)) $loc }
  | a=ident; LBRACK; idx=exp; RBRACK  { mk_node (Larr(a,idx)) $loc }
  ;

%inline quantified_formula:
  | q=quantifier; xs=separated_list(COMMA, quantifier_binding); DOT; f=formula
    { mk_node (Fquant(q,xs,f)) $loc }
  ;

%inline quantifier_binding:
  | x=simple_lident; COLON; t=ty_or_null_ty; e=option(preceded(IN, exp))
    { mk_qbind x t e $loc }
  ;

%inline connective:
  | CONJ { Conj }
  | DISJ { Disj }
  | IMP  { Imp }
  | IFF  { Iff }
  ;

%inline quantifier:
  | FORALL { Forall }
  | EXISTS { Exists }
  ;

%inline modifier:
  | GHOST       { Ghost }
  | PUBLIC      { Public }
  | MODSCOPE    { Modscope }
  ;

effect_elt_desc:
  | id=ident                     { mk_node (`Ident id) $loc }
  | e=exp; IMAGE; f=ident { mk_node (`Image (e, f)) $loc }
  ;

%inline effect_kind:
  | READ    { `Read_effect }
  | WRITE   { `Write_effect }
  | READWRITE   { `Readwrite_effect }
  ;

effect_list_elt:
  | k=effect_kind; es=separated_nonempty_list(COMMA, effect_elt_desc)
    { List.flatten @@
    List.map (fun e -> mk_effect_elt k e.elt $loc) es
    }
  ;

effect_list:
  | es=separated_list(SEMICOLON, effect_list_elt)
    { mk_node (List.flatten es) $loc }
  ;

atomic_command:
  | SKIP { mk_node Skip $loc }
  | HAVOC; x=ident { mk_node (Havoc x) $loc }
  | x=ident; ASSIGN; e=exp { mk_node (Assign(x,e)) $loc }
  | x=ident; ASSIGN; NEW; k=simple_uident { mk_node (New_class(x,k)) $loc }
  | x=ident; ASSIGN; NEW; k=simple_uident; LBRACK; sz=exp; RBRACK
    { mk_node (New_array(x,k,sz)) $loc }
  | y=ident; ASSIGN; x=ident; DOT; f=ident { mk_node (Field_deref(y,x,f)) $loc }
  | x=ident; DOT; f=ident; ASSIGN; e=exp { mk_node (Field_update(x,f,e)) $loc }
  | m=ident; LPAREN; args=separated_list(COMMA, ident); RPAREN
    { mk_node (Call(None,m, List.map (fun e -> mk_node e $loc) args)) $loc }
  | a=ident; LBRACK; e=exp; RBRACK; ASSIGN; e2=exp
    { mk_node (Array_update(a,e,e2)) $loc }
  | x=ident; ASSIGN; a=ident; LBRACK; e=exp; RBRACK
    { mk_node (Array_access(x,a,e)) $loc }
  ;

command:
  | ac=atomic_command
    { mk_node (Acommand(ac)) $loc }
  | ASSUME; LBRACE; f=formula; RBRACE
    { mk_node (Assume(f)) $loc }
  | ASSERT; LBRACE; f=formula; RBRACE
    { mk_node (Assert(f)) $loc }
  | LBRACE; f=formula; RBRACE;
    { mk_node (Assert(f)) $loc }
  | VAR; GHOST; x=simple_lident; COLON; t=ty; IN; c=command
    { mk_node (Vardecl(x,Some Ghost,t,c)) $loc }
  | VAR; x=simple_lident; COLON; t=ty; IN; c=command
    { mk_node (Vardecl(x,None,t,c)) $loc }
  | c1=command; SEMICOLON; c2=command
    { mk_node (Seq(c1,c2)) $loc }
  | IF; e=exp; THEN; c1=command; END
    { let skip_node = mk_node (Acommand (mk_node Skip $loc)) $loc in
      mk_node (If(e,c1,skip_node)) $loc }
  | IF; e=exp; THEN; c1=command; ELSE; c2=command; END
    { mk_node (If(e,c1,c2)) $loc }
  | WHILE; e=exp; DO; s=while_spec; c=command; DONE
    { mk_node (While(e,s,c)) $loc }
  | LPAREN; c=command; RPAREN
    { c }
  | c=command; SEMICOLON { c }
  ;

%inline while_spec:
  | ss=list(while_spec_elt) { ss }
  ;

while_spec_elt:
  | INVARIANT; LBRACE; inv=formula; RBRACE { mk_node (Winvariant inv) $loc }
  | VARIANT; LBRACE; e=exp; RBRACE { mk_node (Wvariant e) $loc }
  | EFFECTS; LBRACE; e=effect_list; RBRACE { mk_node (Wframe e) $loc }
  | EFFECT_WRS;
    LBRACE; es=separated_list(COMMA, effect_elt_desc); RBRACE
    { let es = List.map (fun e -> mk_effect_elt `Write_effect e.elt $loc) es in
      mk_node (Wframe (mk_node (List.flatten es) $loc)) $loc }
  | EFFECT_RDS;
    LBRACE; es=separated_list(COMMA, effect_elt_desc); RBRACE
    { let es = List.map (fun e -> mk_effect_elt `Read_effect e.elt $loc) es in
      mk_node (Wframe (mk_node (List.flatten es) $loc)) $loc }
  ;

spec_elt:
  | REQUIRES; LBRACE; f=formula; RBRACE     { mk_node (Precond(f)) $loc }
  | ENSURES; LBRACE; f=formula; RBRACE      { mk_node (Postcond(f)) $loc }
  | EFFECTS; LBRACE; es=effect_list; RBRACE { mk_node (Effects(es)) $loc }
  | EFFECT_RDS;
    LBRACE; es=separated_nonempty_list(COMMA, effect_elt_desc); RBRACE
    { let es = List.map (fun e -> mk_effect_elt `Read_effect e.elt $loc) es in
      mk_node (Effects (mk_node (List.flatten es) $loc)) $loc }
  | EFFECT_WRS;
    LBRACE; es=separated_nonempty_list(COMMA, effect_elt_desc); RBRACE
    { let es = List.map (fun e -> mk_effect_elt `Write_effect e.elt $loc) es in
      mk_node (Effects (mk_node (List.flatten es) $loc)) $loc }
  | EFFECT_RWS;
    LBRACE; es=separated_nonempty_list(COMMA, effect_elt_desc); RBRACE
    { let es = List.map (fun e ->
              mk_effect_elt `Read_effect e.elt $loc @
              mk_effect_elt `Write_effect e.elt $loc
            ) es in
      mk_node (Effects (mk_node (List.flatten es) $loc)) $loc }
  ;

spec_elts:
  |                          { [] }
  | s=spec_elt; rs=spec_elts { s :: rs }
  ;

spec:
  | s=spec_elts; { mk_node s $loc }
  ;

field_decl:
  | m=modifier; fname=simple_lident; COLON; t=ty; SEMICOLON
    { mk_node { field_name = fname; field_ty = t; attribute = m } $loc }
  | fname=simple_lident; COLON; t=ty; SEMICOLON
    { mk_node { field_name = fname; field_ty = t; attribute = Public } $loc }
  ;

field_decls:
  | fs=list(field_decl) { fs }
  ;

class_decl:
  | CLASS; cname=simple_uident; LBRACE; fs=field_decls; RBRACE
    { mk_node { class_name = cname; fields = fs } $loc }
  ;

class_def:
  | c=class_decl { mk_node (Class c) $loc }
  ;

meth_decl:
  | METH; mname=ident; p=meth_param_list; COLON; rty=ty_or_null_ty; s=spec
    { mk_node (mk_meth_decl mname p rty s) $loc }
  ;

%inline meth_param_list:
  | LPAREN; ps=separated_list(COMMA, meth_param); RPAREN { ps }
  ;

meth_param:
  | m=modifier; x=simple_lident; COLON; t=ty_or_null_ty
    { mk_meth_param_info (Some m) x t }
  | x=simple_lident; COLON; t=ty_or_null_ty
    { mk_meth_param_info None x t }
  ;

ty_or_null_ty:
  | t=ty; { `Non_null t }
  | t=ty; MAYBE_NULL { `Can_be_null t }
  ;

meth_def:
  | m=meth_decl                   { mk_node (Method(m,None)) $loc }
  | m=meth_decl; EQUAL; c=command { mk_node (Method(m,Some c)) $loc }
  ;

inductive_predicate:
  | INDUCTIVE; name=simple_lident;
    LPAREN; ps=separated_list(COMMA, named_formula_param); RPAREN;
    EQUAL; body=inductive_cases
    { mk_node {ind_name=name; ind_params=ps; ind_cases=body} $loc }
  ;

inductive_cases:
  |                                            { [] }
  | BAR; ic=inductive_case; is=inductive_cases { (ic :: is) }
  ;

inductive_case:
  | constr=simple_lident; COLON; f=formula { (mk_node constr $loc,f) }
  ;

named_formula:
  | PREDICATE; name=simple_lident; ps=named_formula_params;
    annot=option(named_formula_annotation); EQUAL; f=formula
    { let inner =
        {kind=`Predicate; annotation=annot; formula_name=name; params=ps; body=f}
      in mk_node inner $loc }
  | PRIVATE; INVARIANT; name=simple_lident; EQUAL; f=formula;
    { let inner = {kind=`Predicate;
                   annotation=Some Private_invariant;
                   formula_name=name;
                   params=[];
                   body=f}
      in mk_node inner $loc }
  | PUBLIC; INVARIANT; name=simple_lident; EQUAL; f=formula;
    { let inner = {kind=`Predicate;
                   annotation=Some Public_invariant;
                   formula_name=name;
                   params=[];
                   body=f}
      in mk_node inner $loc }
  | a=axiom_or_lemma; name=simple_lident; COLON; f=formula
    { mk_node { kind=a; annotation=None; formula_name=name; params=[]; body=f } $loc }
  ;

named_formula_annotation:
  | LBRACK; PUBLIC_INV_ANNOT; RBRACK { Public_invariant }
  | LBRACK; PRIVATE_INV_ANNOT; RBRACK { Private_invariant }
  ;

%inline axiom_or_lemma:
  | AXIOM { `Axiom }
  | LEMMA { `Lemma }
  ;

%inline named_formula_params:
  | LPAREN; ps=separated_list(COMMA, named_formula_param); RPAREN { ps }
  | COLON; { [] }
  ;

named_formula_param:
  | x=simple_lident; COLON; t=ty { (x, t) }
  ;

import_directive:
  | IMPORT; k=import_kind; id=simple_uident; as_name=option(preceded(AS, simple_uident));
    related_by=option(preceded(RELATED,preceded(BY,simple_uident)))
    { let import = {import_kind=k; import_name=id; import_as=as_name; related_by}
      in mk_node import $loc }
  ;

%inline import_kind:
  | (* epsilon *) { Iregular }
  | THEORY        { Itheory }
  ;

extern_decl:
  | EXTERN; TYPE; tid=simple_lident; WITH; DEFAULT; EQUAL; def=simple_lident
    { mk_node (mk_extern_symbol tid Ex_type [] ([],[]) None (Some def)) $loc }
  | EXTERN; PREDICATE; id=simple_lident;
    LPAREN; params=separated_list(COMMA, ty); RPAREN
    { mk_node (mk_extern_symbol id Ex_predicate params ([],[]) None None) $loc }
  | EXTERN; BIPREDICATE; id=simple_lident;
    LPAREN; lparams=separated_list(COMMA, ty); BAR;
            rparams=separated_list(COMMA, ty); RPAREN
    { mk_node (mk_extern_symbol id Ex_bipredicate [] (lparams,rparams) None None) $loc }
  | EXTERN; LEMMA; id=simple_lident
    { mk_node (mk_extern_symbol id Ex_lemma [] ([],[]) None None) $loc }
  | EXTERN; AXIOM; id=simple_lident
    { mk_node (mk_extern_symbol id Ex_axiom [] ([],[]) None None) $loc }
  | EXTERN; CONST; id=simple_lident; COLON; t=ty
    { mk_node (mk_extern_symbol id Ex_const [] ([],[]) (Some t) None) $loc }
  | EXTERN; id=simple_lident; LPAREN; params=separated_list(COMMA, ty); RPAREN;
    COLON; retty=ty
    { mk_node (mk_extern_symbol id Ex_function params ([],[]) (Some retty) None) $loc }
  ;

interface_vardecl:
  | m=public_or_ghost; x=simple_lident; COLON; t=ty
    { (m,x,t) }
  ;

%inline public_or_ghost:
  | PUBLIC { Public }
  | GHOST  { Ghost }
  ;

interface_elt:
  | c=class_decl { mk_node (Intr_cdecl(c)) $loc }
  | m=meth_decl  { mk_node (Intr_mdecl(m)) $loc }
  | n=named_formula { mk_node (Intr_formula(n)) $loc }
  | i=import_directive { mk_node (Intr_import(i)) $loc }
  | v=interface_vardecl
    { let (m,x,t) = v in
      mk_node (Intr_vdecl(m,x,t)) $loc
    }
  | BOUNDARY; LBRACE; es=separated_list(COMMA, effect_elt_desc); RBRACE
    { mk_node
    (Intr_boundary (mk_node (List.map (mk_boundary_elt $loc) es) $loc))
      $loc
    }
  | DATAGROUP; LBRACE; is=separated_list(COMMA, simple_lident); RBRACE
    { mk_node (Intr_datagroup(is)) $loc }
  | e=extern_decl
    { mk_node (Intr_extern e) $loc }
  | i=inductive_predicate { mk_node (Intr_inductive i) $loc }
  ;

interface_elt_list:
  |                                             { [] }
  | i=interface_elt; is=interface_elt_list      { i :: is }
  ;

interface_def:
  | INTERFACE; iname=simple_uident; EQUAL; is=interface_elt_list; END
    { mk_node { intr_name=iname; intr_elts=is } $loc }
  ;

module_def:
  | MODULE; mname=simple_uident; COLON; iname=simple_uident; EQUAL;
    ms=module_elt_list; END
    { mk_node { mdl_name = mname;
                mdl_interface = iname;
                mdl_elts = ms }
      $loc }
  | MODULE; MAIN_MODULE; EQUAL; ms=module_elt_list; END
    { mk_node { mdl_name = Ast.Id "Main";
                mdl_interface = Ast.Id "MAIN";
                mdl_elts = ms }
      $loc }
  ;

module_elt_list:
  |                                     { [] }
  | m=module_elt; ms=module_elt_list    { m :: ms }
  ;

module_elt:
  | c=class_def
    { mk_node (Mdl_cdef c) $loc }
  | m=meth_def
    { mk_node (Mdl_mdef m) $loc }
  | f=named_formula
    { mk_node (Mdl_formula f) $loc }
  | i=import_directive
    { mk_node (Mdl_import i) $loc }
  | m=modifier; x=simple_lident; COLON; t=ty
    { mk_node (Mdl_vdecl(m,x,t)) $loc }
  | d=datagroup_def
    { let (group,flds) = d in
      mk_node (Mdl_datagroup(group,flds)) $loc }
  | e=extern_decl
    { mk_node (Mdl_extern(e)) $loc }
  | i=inductive_predicate
    { mk_node (Mdl_inductive i) $loc }
  ;

datagroup_def:
  | DATAGROUP; g=simple_lident; CONTAINS; fs=separated_list(COMMA, ident) { (g,fs) }
  ;

rformula:
  | rf=rformula1 { rf }
  | b=biexp { mk_node (Rbiexp b) $loc }
  ;

biexp:
  | b1=biexp; op=binop; b2=biexp { mk_node (Bibinop(op,b1,b2)) $loc }
  | v=value_in_state { mk_node (Bivalue v) $loc }
  | LBRACK; c=const_exp; RBRACK { mk_node (Biconst c) $loc }

value_in_state:
  | LEFT_EXP_OPEN; e=exp; LEFT_CLOSE { mk_node (Left e) $loc }
  | RIGHT_OPEN; e=exp; RIGHT_EXP_CLOSE { mk_node (Right e) $loc }
  ;

rformula1:
  | f=ident; LPAREN; us=separated_list(COMMA, exp); BAR;
    vs=separated_list(COMMA, exp); RPAREN
    { let us = List.map (fun e -> mk_node (Left e) $loc) us in
      let vs = List.map (fun e -> mk_node (Right e) $loc) vs in
      mk_node (Rprimitive(f,us @ vs)) $loc }
  | e1=exp; BIEQUAL; e2=exp
    { mk_node (Rbiequal(e1,e2)) $loc }
  | AGREE; x=simple_lident
    { let var_x = mk_node (Evar x) $loc in
      mk_node (Rbiequal(var_x,var_x)) $loc }
  | AGREE; e=exp; IMAGE; f=ident
    { mk_node (Ragree(e,f)) $loc }
  | BOTH; f=formula
    { mk_node (Rboth(f)) $loc }
  | FRM_NOT; r=rformula %prec UMINUS
    { mk_node (Rnot(r)) $loc }
  | LEFT_OPEN; f=formula; LEFT_CLOSE
    { mk_node (Rleft(f)) $loc }
  | RIGHT_OPEN; f=formula; RIGHT_CLOSE
    { mk_node (Rright(f)) $loc }
  | r1=rformula; c=connective; r2=rformula
    { mk_node (Rconn(c,r1,r2)) $loc }
  | r=quantified_rformula %prec IN
    { r }
  | LPAREN; r=rformula; RPAREN
    { r }
  | lrf=let_rformula
    { lrf }
  ;

let_rformula:
  | LET;
    x=simple_lident; xt=option(preceded(COLON, ty)); BAR;
    y=simple_lident; yt=option(preceded(COLON, ty)); EQUAL;
    xval=let_bound_value; BAR; yval=let_bound_value; IN;
    rfrm=rformula
    { let lbind = (x, xt, mk_node {value=xval; is_old=false; is_init=false} $loc) in
      let rbind = (y, yt, mk_node {value=yval; is_old=false; is_init=false} $loc) in
      mk_node (Rlet (Some lbind, Some rbind, rfrm)) $loc }
  | LET;
    x=simple_lident; xt=option(preceded(COLON, ty)); BAR;
    y=simple_lident; yt=option(preceded(COLON, ty)); EQUAL;
    OLD; LPAREN; xval=let_bound_value; RPAREN; BAR; OLD; LPAREN; yval=let_bound_value; RPAREN; IN;
    rfrm=rformula
    { let lbind = (x, xt, mk_node {value=xval; is_old=true; is_init=false} $loc) in
      let rbind = (y, yt, mk_node {value=yval; is_old=true; is_init=false} $loc) in
      mk_node (Rlet (Some lbind, Some rbind, rfrm)) $loc }
  | LET;
    x=simple_lident; xt=option(preceded(COLON, ty)); BAR;
    y=simple_lident; yt=option(preceded(COLON, ty)); EQUAL;
    INIT; LPAREN; xval=let_bound_value; RPAREN; BAR; INIT; LPAREN; yval=let_bound_value; RPAREN; IN;
    rfrm=rformula
    { let lbind = (x, xt, mk_node {value=xval; is_old=false; is_init=true} $loc) in
      let rbind = (y, yt, mk_node {value=yval; is_old=false; is_init=true} $loc) in
      mk_node (Rlet (Some lbind, Some rbind, rfrm)) $loc }

  /* One-sided LETs */
  | LET; x=simple_lident; xt=option(preceded(COLON,ty)); BAR;
    EQUAL; xval=let_bound_value; IN; rfrm=rformula
    { let lbind = (x, xt, mk_node {value=xval; is_old=false; is_init=false} $loc) in
      mk_node (Rlet (Some lbind, None, rfrm)) $loc }
  | LET; x=simple_lident; xt=option(preceded(COLON,ty)); BAR;
    EQUAL; OLD; LPAREN; xval=let_bound_value; RPAREN; IN; rfrm=rformula
    { let lbind = (x, xt, mk_node {value=xval; is_old=true; is_init=false} $loc) in
      mk_node (Rlet (Some lbind, None, rfrm)) $loc }

  | LET; BAR; y=simple_lident; yt=option(preceded(COLON,ty));
    EQUAL; yval=let_bound_value; IN; rfrm=rformula
    { let rbind = (y, yt, mk_node {value=yval; is_old=false; is_init=false} $loc) in
      mk_node (Rlet (None, Some rbind, rfrm)) $loc }
  | LET; BAR; y=simple_lident; yt=option(preceded(COLON,ty)); BAR;
    EQUAL; OLD; LPAREN; yval=let_bound_value; RPAREN; IN; rfrm=rformula
    { let rbind = (y, yt, mk_node {value=yval; is_old=true; is_init=false} $loc) in
      mk_node (Rlet (None, Some rbind, rfrm)) $loc }
  ;

%inline quantified_rformula:
  | q=quantifier; xs=rquantifier_bindings; DOT; r=rformula
    { mk_node (Rquant(q,xs,r)) $loc }
  ;

%inline rquantifier_bindings:
  | xs=separated_list(COMMA, quantifier_binding); BAR;
    ys=separated_list(COMMA, quantifier_binding)
    { (xs,ys) }
  ;

named_rformula:
  | a=axiom_or_lemma; name=simple_lident; COLON; rf=rformula
    { mk_node { kind=a; biformula_name=name; biparams=([],[]);
                body=rf; is_coupling=false } $loc }
  | PREDICATE; name=simple_lident;
    LPAREN; psl=separated_list(COMMA, named_formula_param); BAR;
            psr=separated_list(COMMA, named_formula_param); RPAREN;
    EQUAL; rf=rformula
    { mk_node { kind=`Predicate;
                biformula_name=name;
                biparams=(psl, psr);
                body=rf;
                is_coupling = false; }
      $loc }
  | COUPLING; name=simple_lident; EQUAL; rf=rformula
    { mk_node {kind=`Predicate;
               biformula_name=name;
               biparams=([],[]);
               body=rf;
               is_coupling=true}
      $loc }
  | PREDICATE; name=simple_lident; (* To be removed *)
    LPAREN; psl=separated_list(COMMA, named_formula_param); BAR;
            psr=separated_list(COMMA, named_formula_param); RPAREN;
    LBRACK; COUPLING_ANNOT; RBRACK;
    EQUAL; rf=rformula
    { mk_node { kind=`Predicate;
                biformula_name=name;
                biparams=(psl, psr);
                body=rf;
                is_coupling = true; }
      $loc }

bicommand:
  | BIHAVOC; x=ident; LBRACE; r=rformula; RBRACE
    { mk_node (Bihavoc_right(x,r)) $loc }
  | c1=command; BAR; c2=command
    { mk_node (Bisplit(c1,c2)) $loc }
  | LEFT_SYNC; a=atomic_command; RIGHT_SYNC
    { mk_node (Bisync(a)) $loc }
  | BIVAR; x1=varbind; BAR; x2=varbind; IN; b=bicommand
    { mk_node (Bivardecl(Some x1,Some x2,b)) $loc }
  | BIVAR; x1=varbind; BAR; IN; b=bicommand
    { mk_node (Bivardecl(Some x1,None,b)) $loc }
  | BIVAR; BAR; x2=varbind; IN; b=bicommand
    { mk_node (Bivardecl(None,Some x2,b)) $loc }
  | b1=bicommand; SEMICOLON; b2=bicommand
    { mk_node (Biseq(b1,b2)) $loc }
  | BIIF; e1=exp; BAR; e2=exp; THEN; b1=bicommand; END
    { let skip_node = mk_node Skip $loc in
      let biskip_node = mk_node (Bisync (skip_node)) $loc in
      mk_node (Biif(e1,e2,b1,biskip_node)) $loc }
  | BIIF; e1=exp; BAR; e2=exp; THEN; b1=bicommand; ELSE; b2=bicommand; END
    { mk_node (Biif(e1,e2,b1,b2)) $loc }
  | BIASSUME; LBRACE; r=rformula; RBRACE
    { mk_node (Biassume(r)) $loc }
  | BIASSERT; LBRACE; r=rformula; RBRACE
    { mk_node (Biassert(r)) $loc }
  | LBRACE; LBRACE; r=rformula; RBRACE; RBRACE
    { mk_node (Biassert(r)) $loc }
  | BIWHILE; e1=exp; BAR; e2=exp; DOT; ag=alignment_guard; DO;
    bws=biwhile_spec; b=bicommand; DONE
    { mk_node (Biwhile(e1,e2,ag,bws,b)) $loc }
  | BIWHILERIGHT; e1=exp; DO; bws=biwhile_spec; b=bicommand; DONE
    { let false_node = mk_node Ffalse $loc in
      let rfalse_node = mk_node (Rboth false_node) $loc in
      let true_node = mk_node Ftrue $loc in
      let rtrue_node = mk_node (Rboth true_node) $loc in
      let ag = Some (rfalse_node, rtrue_node) in
      let false_expr = mk_node (Econst (mk_node (Ebool false) $loc)) $loc in
      mk_node (Biwhile(false_expr,e1,ag,bws,b)) $loc }
  | BIWHILELEFT; e1=exp; DO; bws=biwhile_spec; b=bicommand; DONE
    { let false_node = mk_node Ffalse $loc in
      let rfalse_node = mk_node (Rboth false_node) $loc in
      let true_node = mk_node Ftrue $loc in
      let rtrue_node = mk_node (Rboth true_node) $loc in
      let ag = Some (rtrue_node, rfalse_node) in
      let false_expr = mk_node (Econst (mk_node (Ebool false) $loc)) $loc in
      mk_node (Biwhile(e1,false_expr,ag,bws,b)) $loc }
  | BIUPDATE; x1=ident; WITH; x2=ident
    { mk_node (Biupdate(x1,x2)) $loc }
  | b=bicommand_fourwayif { b }
  | LPAREN; b=bicommand; RPAREN
    { b }
  | b=bicommand; SEMICOLON { b }
  ;

bicommand_fourwayif:
  | BIIFFOUR; e1=exp; BAR; e2=exp;
    BITHENTHEN; b1=bicommand;
    BITHENELSE; b2=bicommand;
    BIELSETHEN; b3=bicommand;
    BIELSEELSE; b4=bicommand; END
    { mk_node (Biif4(e1, e2, b1, b2, b3, b4)) $loc }
  ;

%inline biwhile_spec:
  | ss=list(biwhile_spec_elt) { ss }
  ;

biwhile_spec_elt:
  | INVARIANT; LBRACE; rf=rformula; RBRACE
    { mk_node (Biwinvariant rf) $loc }
  | EFFECTS; LBRACE; e1=effect_list; BAR; e2=effect_list; RBRACE
    { mk_node (Biwframe (e1, e2)) $loc }
  | VARIANT; LBRACE; e=biexp; RBRACE
    { mk_node (Biwvariant e) $loc }
  ;

varbind:
  | GHOST; x=simple_lident; COLON; t=ty { (x,Some Ghost,t) }
  | x=simple_lident; COLON; t=ty        { (x,None,t) }
  ;

alignment_guard:
  |                                     { None }
  | r1=rformula; BAR; r2=rformula       { Some(r1,r2) }
  ;

bispec_elt:
  | REQUIRES; LBRACE; rf=rformula; RBRACE
    { mk_node (Biprecond (rf)) $loc }
  | ENSURES; LBRACE; rf=rformula; RBRACE
    { mk_node (Bipostcond (rf)) $loc }
  | EFFECTS; LBRACE; es=effect_list; BAR; es2=effect_list; RBRACE
    { mk_node (Bieffects (es, es2)) $loc }
  ;

bispec:
  | bs=list(bispec_elt) { mk_node bs $loc }
  ;

bimeth_decl:
  | METH; mname=ident; LPAREN;
    psl=separated_list(COMMA, meth_param); BAR
    psr=separated_list(COMMA, meth_param); RPAREN;
    COLON;
    LPAREN; retl=ty_or_null_ty; BAR; retr=ty_or_null_ty; RPAREN;
    bs=bispec
    { let meth_decl = mk_bimeth_decl mname psl psr retl retr bs in
      mk_node meth_decl $loc }
  ;

bimeth_def:
  | b=bimeth_decl
    { mk_node (Bimethod (b, None)) $loc }
  | b=bimeth_decl; EQUAL; cc=bicommand
    { mk_node (Bimethod (b, Some cc)) $loc }
  | b=bimeth_decl; LBRACK; cc=bicommand; RBRACK
    { mk_node (Bimethod (b, Some cc)) $loc }
  ;

bimodule_elt:
  | mdef=bimeth_def    { mk_node (Bimdl_mdef mdef) $loc }
  | e=extern_decl      { mk_node (Bimdl_extern e) $loc }
  | i=import_directive { mk_node (Bimdl_import i) $loc }
  | nf=named_rformula  { mk_node (Bimdl_formula nf) $loc }
  ;

bimodule_def:
  | BIMODULE; bmdlname=simple_uident;
    LPAREN; left_mdl=simple_uident; BAR; right_mdl=simple_uident; RPAREN;
    EQUAL; bs=list(bimodule_elt); END
    { mk_node {
      bimdl_name = bmdlname;
      bimdl_left_impl = left_mdl;
      bimdl_right_impl = right_mdl;
      bimdl_elts = bs
    }
      $loc
    }
  ;

%inline program_elt:
  | i=interface_def     { mk_node (Unr_intr i) $loc }
  | m=module_def        { mk_node (Unr_mdl m) $loc }
  | b=bimodule_def      { mk_node (Rel_mdl b) $loc }
  ;

program:
  | { [] }
  | p=program_elt; ps=program { p :: ps }
  ;
