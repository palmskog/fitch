%{
open Util
open Fitch_system
open FitchDecidableNat
open FitchProp
%}

%token <string> IDENT
%token <int> INT
%token COMMA DASH LPAREN RPAREN LBRACKET RBRACKET
%token NOT AND OR IMPLIES VDASH
%token CONT ASSUMPTION PREMISE LEM COPY ANDI ANDE1 ANDE2
%token ORI1 ORI2 IMPE NEGE CONTE NEGNEGI NEGNEGE MT
%token IMPI NEGI ORE PBC
%token EOF

%right IMPLIES
%left AND
%left OR
%right NOT

%start main
%type <char list Fitch_system.FitchDecidableNat.FitchProp.claim> main

%%

main:
  claim EOF { $1 }
;

claim:
  judgment list(entry) { Coq_claim_judgment_proof ($1, $2) }
;

judgment:
  separated_list(COMMA, prop) VDASH prop { Coq_judgment_follows ($1, $3) }
;

prop:
  CONT { Coq_prop_cont }
| NOT prop { Coq_prop_neg $2 }
| IDENT { Coq_prop_p (char_list_of_string $1) }
| prop AND prop { Coq_prop_and ($1, $3) }
| prop OR prop { Coq_prop_or ($1, $3) }
| prop IMPLIES prop { Coq_prop_imp ($1, $3) }
| LPAREN prop RPAREN { $2 }
;

entry:
  derivation { Coq_entry_derivation $1 }
| LBRACKET list(entry) RBRACKET { Coq_entry_box $2 }
;

derivation:
  INT prop reason { Coq_derivation_deriv ($1, $2, $3) }
;

reason:
  ASSUMPTION { Coq_reason_assumption }
| justification { Coq_reason_justification $1 }
;

justification:
  PREMISE { Coq_justification_premise }
| LEM { Coq_justification_lem }
| COPY INT { Coq_justification_copy $2 }
| ANDI INT COMMA INT { Coq_justification_andi ($2, $4) }
| ANDE1 INT { Coq_justification_ande1 $2 }
| ANDE2 INT { Coq_justification_ande2 $2 }
| ORI1 INT { Coq_justification_ori1 $2 }
| ORI2 INT { Coq_justification_ori2 $2 }
| IMPE INT COMMA INT { Coq_justification_impe ($2, $4) }
| NEGE INT COMMA INT { Coq_justification_nege ($2, $4) }
| CONTE INT { Coq_justification_conte $2 }
| NEGNEGI INT { Coq_justification_negnegi $2 }
| NEGNEGE INT { Coq_justification_negnege $2 }
| MT INT COMMA INT { Coq_justification_mt ($2, $4) }
| IMPI INT DASH INT { Coq_justification_impi ($2, $4) }
| NEGI INT DASH INT { Coq_justification_negi ($2, $4) }
| ORE INT COMMA INT DASH INT COMMA INT DASH INT { Coq_justification_ore ($2, $4, $6, $8, $10) }
| PBC INT DASH INT { Coq_justification_pbc ($2, $4) }
;
