{

open Lexing
open Parser

exception Lexer_error of string

let symbols = Hashtbl.of_seq @@ List.to_seq [
    ("ghost", GHOST);
    ("public", PUBLIC);
    ("private", PRIVATE);
    ("modscope", MODSCOPE);

    ("null", NULL);
    ("true", TRUE);
    ("false", FALSE);

    ("by", BY);
    ("related", RELATED);

    ("(", LPAREN);
    (")", RPAREN);
    (",", COMMA);
    (":", COLON);
    (";", SEMICOLON);
    ("{", LBRACE);
    ("}", RBRACE);
    ("[", LBRACK);
    ("]", RBRACK);
    (".", DOT);
    ("+", PLUS);
    ("?", MAYBE_NULL);
    ("-", MINUS);
    ("*", MULT);
    ("/", DIV);
    ("mod", MOD);
    ("`", IMAGE);
    ("=", EQUAL);
    ("<>", NOTEQUAL);
    ("<=", LEQ);
    ("<", LT);
    (">=", GEQ);
    (">", GT);
    ("#", DISJOINT);
    ("union", UNION);
    ("inter", INTER);
    ("diff", DIFF);
    ("in", IN);
    ("notin", NOTIN);
    ("subset", SUBSETEQ);
    ("of", SUBRGN);
    ("not", NOT);
    ("and", AND);
    ("&&", AND);
    ("or", OR);
    ("||", OR);

    ("True", FRM_TRUE);
    ("False", FRM_FALSE);
    ("Type", FRM_TYPE);
    ("~", FRM_NOT);
    ("/\\", CONJ);
    ("\\/", DISJ);
    ("NOT", FRM_NOT);
    ("AND", CONJ);
    ("OR", DISJ);
    ("->", IMP);
    ("<->", IFF);
    ("let", LET);
    ("old", OLD);
    ("init", INIT);
    ("forall", FORALL);
    ("exists", EXISTS);

    ("skip", SKIP);
    (":=", ASSIGN);
    ("havoc", HAVOC);
    ("new", NEW);
    ("var", VAR);
    ("if", IF);
    ("then", THEN);
    ("else", ELSE);
    ("while", WHILE);
    ("do", DO);
    ("done", DONE);
    ("assume", ASSUME);
    ("assert", ASSERT);
    ("invariant", INVARIANT);
    ("variant", VARIANT);

    ("rd", READ);
    ("wr", WRITE);
    ("rw", READWRITE);
    ("requires", REQUIRES);
    ("ensures", ENSURES);
    ("effects", EFFECTS);
    ("reads", EFFECT_RDS);
    ("writes", EFFECT_WRS);
    ("reads/writes", EFFECT_RWS);

    ("meth", METH);
    ("class", CLASS);
    ("interface", INTERFACE);
    ("end", END);

    ("predicate", PREDICATE);
    ("inductive", INDUCTIVE);
    ("bipredicate", BIPREDICATE);
    ("coupling", COUPLING);
    ("axiom", AXIOM);
    ("lemma", LEMMA);

    ("import", IMPORT);
    ("theory", THEORY);
    ("as", AS);
    ("boundary", BOUNDARY);
    ("datagroup", DATAGROUP);
    ("contains", CONTAINS);

    ("module", MODULE);
    ("bimodule", BIMODULE);

    ("|", BAR);
    ("<|", LEFT_OPEN);
    ("[<", LEFT_EXP_OPEN);
    ("<]", LEFT_CLOSE);
    ("[>", RIGHT_OPEN);
    ("|>", RIGHT_CLOSE);
    (">]", RIGHT_EXP_CLOSE);
    ("=:=", BIEQUAL);
    ("|_", LEFT_SYNC);
    ("_|", RIGHT_SYNC);

    ("Agree", AGREE);
    ("Both", BOTH);

    ("HavocR", BIHAVOC);
    ("Var", BIVAR);
    ("If", BIIF);
    ("While", BIWHILE);
    ("WhileL", BIWHILELEFT);
    ("WhileR", BIWHILERIGHT);
    ("Assume", BIASSUME);
    ("Assert", BIASSERT);
    ("Link", BIUPDATE);
    ("Connect", BIUPDATE);
    ("with", WITH);

    ("If4", BIIFFOUR);
    ("thenThen", BITHENTHEN);
    ("thenElse", BITHENELSE);
    ("elseThen", BIELSETHEN);
    ("elseElse", BIELSEELSE);

    ("extern", EXTERN);
    ("type", TYPE);
    ("const", CONST);
    ("default", DEFAULT);

    ("Main", MAIN_MODULE);
  ]

let annots = Hashtbl.of_seq @@ List.to_seq [
    ("public", PUBLIC_INV_ANNOT);
    ("private", PRIVATE_INV_ANNOT);
    ("coupling", COUPLING_ANNOT)
  ]

let is_uppercase_ident str =
  let ini = str.[0] in
  Char.uppercase_ascii ini = ini

let mk_token lexbuf =
  let str = lexeme lexbuf in
  try (Hashtbl.find symbols str)
  with _ ->
    if is_uppercase_ident str
    then UIDENT str
    else LIDENT str

let mk_annotation lexbuf =
  let str = lexeme lexbuf in
  try (Hashtbl.find annots str)
  with _ -> raise (Lexer_error ("Expected annotation: " ^ Lexing.lexeme lexbuf))

}

let newline = '\n' | ('\r' '\n') | '\r'
let lowercase = ['a'-'z']
let uppercase = ['A'-'Z']
let character = uppercase | lowercase
let whitespace = ['\t' ' ']
let digit = ['0'-'9']

rule token = parse
  | eof { EOF }
  | whitespace { token lexbuf }
  | newline { new_line lexbuf; token lexbuf }
  | "/*" { comments 0 lexbuf }
  | '(' | ')' | '{' | '}' | '[' | ']' | ':' | ';' | '?'
  | '+' | '-' | '*' | '/' | '`' | '~' | "&&" | "||"
  | '=' | '<' | '>' | "<=" | ">=" | "<>"
  | '.' | "/\\" | "\\/" | "->" | "<->"
  | '#' | ',' | "==" | ":=" | "|" | "=:="
  | "<|" | "<]" | "[>" | "|>" | "|_" | "_|" | "[<" | ">]" { mk_token lexbuf }
  | '%' { annotations lexbuf }
  | character (digit | character | '_' | '\'' )* { mk_token lexbuf }
(*  | character (digit | character | '_' | '\'' | '/')* { mk_token lexbuf } *)
  | digit+ { INT (int_of_string (lexeme lexbuf)) }
  | _ { raise @@ Lexer_error ("Unexpected char: " ^ Lexing.lexeme lexbuf) }

and comments level = parse
  | "*/" { if level = 0 then token lexbuf else comments (level-1) lexbuf }
  | "/*" { comments (level+1) lexbuf }
  | newline { new_line lexbuf; comments level lexbuf }
  | eof  { raise @@ Lexer_error ("Comment not closed") }
  | _    { comments level lexbuf }

and annotations = parse
  | whitespace { annotations lexbuf }
  | character (digit | character | '_' | '\'' | '/')* { mk_annotation lexbuf }
  | _ { token lexbuf }
