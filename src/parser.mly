/* Joseph Cutler, 2021 */
%{
open Syntax
%}

/* Surface syntax tokens */
%token <Support.CodeLoc.t * string> ID
%token <Support.CodeLoc.t * bool> VBOOL
%token <Support.CodeLoc.t * int> VNAT
%token <Support.CodeLoc.t * float> VFLOAT
%token <Support.CodeLoc.t> WILD
%token <Support.CodeLoc.t> VUNIT
%token <Support.CodeLoc.t> LAM
%token <Support.CodeLoc.t> ILAM
%token <Support.CodeLoc.t> TLAM
%token <Support.CodeLoc.t> DOT
%token <Support.CodeLoc.t> COLON
%token <Support.CodeLoc.t> LPAREN RPAREN
%token <Support.CodeLoc.t> LBRACK RBRACK
%token <Support.CodeLoc.t> LCBRACE RCBRACE
%token <Support.CodeLoc.t> LANGLE RANGLE
%token <Support.CodeLoc.t> CLAM
%token <Support.CodeLoc.t> COMMA
%token <Support.CodeLoc.t> TYPE
%token <Support.CodeLoc.t> IDX
%token <Support.CodeLoc.t> LET
%token <Support.CodeLoc.t> IN
%token <Support.CodeLoc.t> DO
%token <Support.CodeLoc.t> EQ
%token <Support.CodeLoc.t> FST SND
%token <Support.CodeLoc.t> INL INR
%token <Support.CodeLoc.t> CASE
%token <Support.CodeLoc.t> FIX
%token <Support.CodeLoc.t> NIL
%token <Support.CodeLoc.t> CONS
%token <Support.CodeLoc.t> PACK
%token <Support.CodeLoc.t> UNPACK
%token <Support.CodeLoc.t> PIPE
%token <Support.CodeLoc.t> OF
%token <Support.CodeLoc.t> CLET
%token <Support.CodeLoc.t> RET
%token <Support.CodeLoc.t> BIND
%token <Support.CodeLoc.t> TICK
%token <Support.CodeLoc.t> PHI
%token <Support.CodeLoc.t> STORE
%token <Support.CodeLoc.t> RELEASE
%token <Support.CodeLoc.t> SHIFT
%token <Support.CodeLoc.t> ABSURD
%token <Support.CodeLoc.t> IF
%token <Support.CodeLoc.t> THEN
%token <Support.CodeLoc.t> ELSE
%token <Support.CodeLoc.t> SUM
%token <Support.CodeLoc.t> CONST
%token <Support.CodeLoc.t> QMARK
%token <Support.CodeLoc.t> REAL
%token EOF

/* Type syntax tokens */
%token <Support.CodeLoc.t> TYBOOL
%token <Support.CodeLoc.t> TYNAT
%token <Support.CodeLoc.t> TYUNIT
%token <Support.CodeLoc.t> RARROW
%token <Support.CodeLoc.t> LARROW
%token <Support.CodeLoc.t> FAT_LARROW
%token <Support.CodeLoc.t> FAT_RARROW
%token <Support.CodeLoc.t> GEQ
%token <Support.CodeLoc.t> PLUS
%token <Support.CodeLoc.t> MINUS
%token <Support.CodeLoc.t> AMP
%token <Support.CodeLoc.t> DAMP /* double ampersand && */
%token <Support.CodeLoc.t> BANG
%token <Support.CodeLoc.t> STAR
%token <Support.CodeLoc.t> IFORALL
%token <Support.CodeLoc.t> IEXISTS
%token <Support.CodeLoc.t> TFORALL
%token <Support.CodeLoc.t> LIST
%token <Support.CodeLoc.t> MONAD


%left <Support.CodeLoc.t> PLUS
%left <Support.CodeLoc.t> STAR
%left <Support.CodeLoc.t> AMP
%right <Support.CodeLoc.t> RARROW
%right <Support.CodeLoc.t> CONS

/* Sort syntax tokens */
%token <Support.CodeLoc.t> SONAT
%token <Support.CodeLoc.t> SOPOSREAL
%token <Support.CodeLoc.t> SOPOTVEC

%start pgm
%type <Syntax.la_exp> exp
%type <Syntax.la_type> typ
%type <Syntax.la_sort> sort
%type <Syntax.la_kind> kind
%type <Syntax.la_idx_term> iterm
%type <Syntax.la_decl> decl
%type <Syntax.la_pgm> pgm

%%

kind:
 STAR
   {KStar}
| sort FAT_RARROW kind
   {KArr($1,$3)}
| LPAREN kind RPAREN
    {$2}

la_ident:
  ID
    {let (_,x) = $1 in {ident_source_name = x; ident_fresh_name = `Unfreshened}}

la_ident_binder:
  la_ident
    {Name $1}
| WILD
    {Wild}

la_toplevel_ident:
  ID
    {let (_,x) = $1 in {ident_source_name = x; ident_fresh_name = `TopLevel x}}

pgm:
   decl pgm
     {$1 :: $2}
 | decl
     {[$1]}

decl:
   LET la_toplevel_ident COLON typ EQ exp
     {ValDec ($2,$6,$4)}
 | TYPE la_alias_type_var COLON kind EQ typ
     {TyDec($2,$6,$4)}
 | IDX la_alias_idx_var COLON sort EQ iterm
     {IdxDec($2,$6,$4)}
| DO la_toplevel_ident COLON MONAD LPAREN iterm COMMA iterm RPAREN typ LARROW exp
     {DoDec($2,$6,$8,$10,$12)}

/* Syntax rules */

exp :
   LAM la_ident_binder DOT exp
     {Lam($2,$4)}
 | LET LPAREN la_ident_binder COMMA la_ident_binder RPAREN EQ exp IN exp
     {PLet($8,$3,$5,$10)}
 | LET BANG la_ident_binder EQ exp IN exp
     {LetBang($5,$3,$7)}
 | LET la_ident_binder EQ exp IN exp
     {Let($4,$2,$6)}
 | LET la_ident_binder COLON typ EQ exp IN exp
     {Let(Ann($6,$4),$2,$8)}
 | CASE exp OF la_ident_binder FAT_RARROW exp PIPE la_ident_binder FAT_RARROW exp /* sumcase */
     {SCase($2,$4,$6,$8,$10)}
   /* case xs of nil => _ | x::xs[j] => _*/
 | CASE exp OF NIL FAT_RARROW exp PIPE la_ident_binder CONS la_ident_binder FAT_RARROW exp /* listcase */
     {LCase($2,$6,$8,$10,$12)}
 | CASE exp OF VNAT FAT_RARROW exp PIPE ID LPAREN la_ident_binder RPAREN FAT_RARROW exp
     {match $4,$8 with
        (_,0),(_,"S") -> NCase($2,$6,$10,$13)
      | _ -> (raise Parsing.Parse_error)
     }
 | FIX la_ident_binder EQ exp
     {Fix($2,$4)}
 | ILAM la_idx_var_binder DOT exp
     {ILam($2,$4)}
 | TLAM la_type_var_binder DOT exp
     {TLam($2,$4)}
 | UNPACK LPAREN la_idx_var_binder COMMA la_ident_binder RPAREN EQ exp IN exp
     {Unpack($8,$3,$5,$10)}
 | CLAM DOT exp
     {CLam $3}
 | CLET la_ident_binder EQ exp IN exp
     {CLet($4,$2,$6)}
 | BIND la_ident_binder EQ exp IN exp
     {Bind($4,$2,$6)}
 | RELEASE la_ident_binder EQ exp IN exp
     {Release($4,$2,$6)}
 | IF exp THEN exp ELSE exp
     {Ite($2,$4,$6)}
 | binop_exp_1
     {$1}

binop_exp_1:
   binop_exp_1 PLUS binop_exp_1
     {Binop(BopPlus,$1,$3)}
 | binop_exp_2
     {$1}


binop_exp_2:
   binop_exp_2 CONS binop_exp_2
     {Cons($1,$3)}
 | app_exp
     {$1}

app_exp:
   app_exp atom_exp
     {App($1,$2)}
 | app_exp LBRACK iterm RBRACK
     {IApp ($1,$3)}
 | app_exp LCBRACE typ RCBRACE
     {TApp ($1,$3)}
 | app_exp LBRACK RBRACK
     {CApp $1}
 | unary_exp
     {$1}

unary_exp:
   FST atom_exp
     {Fst $2}
 | SND atom_exp
     {Snd $2}
 | INL atom_exp
     {Inl $2}
 | INR atom_exp
     {Inr $2}
 | BANG atom_exp
     {Bang $2}
 | PACK LBRACK iterm RBRACK atom_exp
     {Pack ($3,$5)}
 | RET atom_exp
     {Ret $2}
 | STORE LBRACK iterm PIPE iterm RBRACK atom_exp
     {Store ($3,$5,$7)}
 | STORE LBRACK iterm RBRACK atom_exp
     {StoreConst ($3,$5)}
 | SHIFT atom_exp
     {Shift $2}
 | atom_exp
     {$1}

atom_exp:
   LPAREN exp RPAREN
     {$2}
 | QMARK
     {Hole}
 | LPAREN exp COLON typ RPAREN
     {Ann($2,$4)}
 | LPAREN exp COMMA exp RPAREN
     {PPair($2,$4)}
 | LPAREN exp AMP exp RPAREN
     {NPair($2,$4)}
 | LANGLE exp RANGLE
     {CPair $2}
 | TICK LBRACK iterm PIPE iterm RBRACK
     {Tick ($3,$5)}
 | ABSURD
     {Absurd}
 | NIL
     {Nil}
 | VNAT
     {let (_,n) = $1 in Const (NConst n)}
 | VUNIT
     {Const UConst}
 | VBOOL
     {let (_,b) = $1 in Const (BConst b)}
 | la_ident
     { Var($1) }

/*
pot_vec:
   pot_vec_lit
     {PVec $1}
 | CONST LPAREN iterm RPAREN
     {PConstVec $3}
 | pot_vec PLUS pot_vec
     {PVecPlus($1,$3)}
 | la_pot_vec_var
     {PVecVar $1}

pot_vec_lit:
   VFLOAT COMMA pot_vec_lit
     {$1 :: $3}
 | VFLOAT
     {[$1]}

la_pot_vec_var:
  ID
    {{pot_source_name = $1; pot_fresh_name = `Unfreshened}}
*/

sort:
   base_sort RARROW sort
     {SoArr($1,$3)}
 | base_sort
     {SoBase $1}

base_sort:
   SONAT
     {SoNat}
 | SOPOSREAL
     {SoPosReal}
 | SOPOTVEC
     {SoPotVec}


/* index terms */
iterm:
    ILAM la_idx_var_binder COLON base_sort DOT iterm
      {IFamLam($2,$4,$6)}
  | binop_iterm_1
      {$1}

binop_iterm_1:
    binop_iterm_1 PLUS binop_iterm_1
      {IPlus($1,$3)}
  | binop_iterm_1 MINUS binop_iterm_1
      {IMinus($1,$3)}
  | binop_iterm_2
      {$1}

binop_iterm_2:
    VFLOAT STAR app_iterm
      {let (_,f) = $1 in IMult(ICReal f,$3)}
  | VNAT STAR app_iterm
      {let (_,n) = $1 in IMult(ICNat n,$3)}
  | app_iterm
      {$1}

app_iterm:
    app_iterm atom_iterm
      {IFamApp($1,$2)}
  | atom_iterm
      {$1}

atom_iterm:
    la_idx_var
      {IVar $1}
  | REAL atom_iterm
       {INtoR $2}
  | SUM LPAREN la_idx_var_binder DOT iterm COMMA LCBRACE iterm COMMA iterm RCBRACE RPAREN
      {ISum($3,$5,$8,$10)}
  | VNAT
      {let (_,n) = $1 in IConst (ICNat n)}
  | VFLOAT
      {let (_,f) = $1 in IConst (ICReal f)}
 | CONST LPAREN iterm RPAREN
     {IConstVec $3}
  | LBRACK pot_vec_lit RBRACK
      {IConst (ICPVec $2)}
  | LPAREN iterm RPAREN
      {$2}

pot_vec_lit:
   VFLOAT COMMA pot_vec_lit
     {let (_,f) = $1 in f :: $3}
 | VFLOAT
     {let (_,f) = $1 in [f]}


la_idx_var:
  ID
    {(let (_,s) = $1 in {idx_source_name = s; idx_fresh_name = `Unfreshened} : la_idx_var)}

la_idx_var_binder:
  la_idx_var
    {IName $1}
| WILD
    {IWild}

/* constraints */
constr:
   iterm EQ iterm
     {Eq($1,$3)}
 | iterm FAT_LARROW iterm
     {Leq($1,$3)}
 | iterm GEQ iterm
     {Leq($3,$1)}
 | iterm LANGLE iterm
     {Lt($1,$3)}
 | iterm RANGLE iterm
     {Lt($3,$1)}
 | LPAREN constr RPAREN
     {$2}

/* Type rules */
typ:
   IFORALL la_idx_var_binder COLON sort DOT typ
     {ty_i_forall $2 $4 $6}
 | IEXISTS la_idx_var_binder COLON sort DOT typ
     {ty_i_exists $2 $4 $6}
 | TFORALL la_type_var_binder COLON kind DOT typ
     {ty_t_forall $2 $4 $6}
 /* perhaps the wrong precedence for this?? */
 | LANGLE constr RANGLE FAT_RARROW typ /* <c> => t */
     {ty_implies $2 $5}
 | ILAM la_idx_var_binder COLON sort DOT typ
     {ty_fam_lam $2 $4 $6}
 | typ_1
     {$1}

typ_1:
   typ_1 RARROW typ_1
     {ty_arr $1 $3}
 | typ_2
     {$1}

typ_2:
   typ_2 PLUS typ_2
     {ty_sum $1 $3}
 | typ_3
     {$1}

typ_3:
   typ_3 STAR typ_3
     {ty_tensor $1 $3}
 | typ_3 AMP typ_3
     {ty_with $1 $3}
 | app_typ
     {$1}

app_typ:
   app_typ LBRACK iterm RBRACK
     {ty_fam_app $1 $3}
 | atom_typ
     {$1}
     

atom_typ:
   TYBOOL
     { ty_bool }
 | TYUNIT
     { ty_unit }
 | TYNAT
     { ty_nat }
 | BANG atom_typ
     {ty_bang $2}
 | la_type_var
     {ty_var $1}
 | LANGLE constr COMMA typ RANGLE /* <c,t> */
     {ty_conj $2 $4}
 | LIST LPAREN iterm COMMA typ RPAREN
     {ty_list $3 $5}
 | MONAD LPAREN iterm PIPE iterm RPAREN atom_typ
     {ty_monad $3 $5 $7}
 | LBRACK iterm PIPE iterm RBRACK atom_typ
     {ty_pot $2 $4 $6}
 | LBRACK iterm RBRACK atom_typ
     {ty_const_pot $2 $4}
 | LPAREN typ RPAREN
     { $2 }

la_type_var:
  ID
    {let (_,s) = $1 in {type_source_name = s; type_fresh_name = `Unfreshened}}

la_type_var_binder:
  la_type_var
    {TName $1}
| WILD
    {TWild}

la_alias_type_var:
  ID
    {let (_,s) = $1 in {type_source_name = s; type_fresh_name = `Alias s}}

la_alias_idx_var:
  ID
    {let (_,s) = $1 in {idx_source_name = s; idx_fresh_name = `Alias s}}

