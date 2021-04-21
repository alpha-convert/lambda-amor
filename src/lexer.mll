(* Joseph Cutler, 2021 *)
{
open Parser
let sym_list = [
  ("_",fun i -> WILD i);
  ("()",fun i -> VUNIT i);
  ("lam",fun i -> LAM i);
  ("ILam",fun i -> ILAM i);
  ("TLam",fun i -> TLAM i);
  ("CLam",fun i -> CLAM i);
  (".",fun i -> DOT i);
  (":",fun i -> COLON i);
  ("(",fun i -> LPAREN i);
  ("[",fun i -> LBRACK i);
  ("]",fun i -> RBRACK i);
  (")",fun i -> RPAREN i);
  (",",fun i -> COMMA i);
  ("let",fun i -> LET i);
  ("do",fun i -> DO i);
  ("type",fun i -> TYPE i);
  ("in",fun i -> IN i);
  ("=",fun i -> EQ i);
  ("fst",fun i -> FST i);
  ("snd",fun i -> SND i);
  ("inl",fun i -> INL i);
  ("inr",fun i -> INR i);
  ("case",fun i -> CASE i);
  ("fix",fun i -> FIX i);
  ("nil",fun i -> NIL i);
  ("::",fun i -> CONS i);
  ("true",fun i -> VBOOL (i,true));
  ("false",fun i -> VBOOL (i,false));
  ("of",fun i -> OF i);
  ("|",fun i -> PIPE i);
  ("pack",fun i -> PACK i);
  ("unpack",fun i -> UNPACK i);
  ("CLet",fun i -> CLET i);
  ("{",fun i -> LCBRACE i);
  ("}",fun i -> RCBRACE i);
  ("<",fun i -> LANGLE i);
  (">",fun i -> RANGLE i);
  ("ret",fun i -> RET i);
  ("bind",fun i -> BIND i);
  ("tick",fun i -> TICK i);
  ("store",fun i -> STORE i);
  ("release",fun i -> RELEASE i);
  ("shift",fun i -> SHIFT i);
  ("absurd",fun i -> ABSURD i);
  ("if",fun i -> IF i);
  ("then",fun i -> THEN i);
  ("else",fun i -> ELSE i);
  ("sum",fun i -> SUM i);
  ("?",fun i -> QMARK i);
  ("real",fun i -> REAL i);
  ("idx",fun i -> IDX i);


  ("Nat",fun i -> SONAT i);
  ("Real",fun i -> SOPOSREAL i);
  ("PotVec",fun i -> SOPOTVEC i);

  ("bool",fun i -> TYBOOL i);
  ("nat",fun i -> TYNAT i);
  ("unit",fun i -> TYUNIT i);
  ("->",fun i -> RARROW i);
  ("<-",fun i -> LARROW i);
  ("<=",fun i -> FAT_LARROW i);
  ("=>",fun i -> FAT_RARROW i);
  (">=",fun i -> GEQ i);
  ("&",fun i -> AMP i);
  ("&&",fun i -> DAMP i);
  ("!",fun i -> BANG i);
  ("+",fun i -> PLUS i);
  ("-",fun i -> MINUS i);
  ("*",fun i -> STAR i);
  ("Iforall",fun i -> IFORALL i);
  ("Iexists",fun i -> IEXISTS i);
  ("Tforall",fun i -> TFORALL i);
  ("List",fun i -> LIST i);
  ("M",fun i -> MONAD i);
  ("phi",fun i -> PHI i);
  ("const",fun i -> CONST i);
]

let filename = ref ""
let lineno = ref 1
let start = ref 0

let newline lexbuf = incr lineno; start := (Lexing.lexeme_start lexbuf)

let info lexbuf =
  Support.CodeLoc.loc (!filename) (!lineno) (Lexing.lexeme_start lexbuf - !start)

type buildfun = Support.CodeLoc.t -> Parser.token
let sym_table : (string,buildfun) Hashtbl.t = Hashtbl.create 1024
let _ =
  List.iter (fun (s,t) -> Hashtbl.add sym_table s t) sym_list

let try_sym i s =
  try (Hashtbl.find sym_table s) i 
  with _ -> Parser.ID (i,s)

let text = Lexing.lexeme

let loc lexbuf =
  Support.CodeLoc.loc (!filename) (!lineno) (Lexing.lexeme_start lexbuf - !start)


}

rule main = parse
(* Whitespace *)
  [' ' '\009' '\012']+     { main lexbuf }
| "\n" { lineno := !lineno + 1; main lexbuf}
| [' ' '\009' '\012']*("\r")  {main lexbuf}

| ['0'-'9']+ '.' ['0'-'9']*
    { Parser.VFLOAT (loc lexbuf,float_of_string (text lexbuf)) }

| ['0'-'9']+
    { Parser.VNAT (loc lexbuf,int_of_string (text lexbuf)) }

(* Variables and reserved words *)
| ['A'-'Z' 'a'-'z']
  ['A'-'Z' 'a'-'z' '_' '0'-'9' '\'']* {try_sym  (info lexbuf) (text lexbuf)}

(* Multichar symbols *)
| "::" | "()" | "->" | "<-" | "<=" | "=>" | ">=" | "&&" { try_sym (info lexbuf) (text lexbuf)}

| ['_' '.' ':' '(' ')' '[' ']' ',' '=' '!' '&' '+' '-' '?' '*' '|' '{' '}' '<' '>'] {try_sym (info lexbuf) (text lexbuf)}

| eof {EOF}
