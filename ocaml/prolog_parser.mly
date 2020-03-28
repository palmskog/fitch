%{
open Util
open Fitch_system
open FitchProgramMap
open FitchPI
%}

%token <string> IDENT
%token <int> INT
%token COMMA LPAREN RPAREN LBRACKET RBRACKET
%token NEG AND OR IMP PERIOD
%token CONT ASSUMPTION PREMISE LEM COPY ANDINT ANDEL1 ANDEL2
%token ORINT1 ORINT2 IMPEL NEGEL CONTEL NEGNEGINT NEGNEGEL MT
%token IMPINT NEGINT OREL PBC
%token EOF

%start main
%type <char list Fitch_system.FitchProgramMap.FitchPI.claim> main

%%

main:
  claim EOF { $1 }
;

claim:
  judgment LBRACKET separated_list(COMMA, entry) RBRACKET PERIOD { Coq_claim_judgment_proof ($1, $3) }
;

judgment:
  LBRACKET separated_list(COMMA, prop) RBRACKET PERIOD prop PERIOD { Coq_judgment_follows ($2, $5) }
;

prop:
  CONT { Coq_prop_cont }
| NEG LPAREN prop RPAREN { Coq_prop_neg $3 }
| IDENT { Coq_prop_p (char_list_of_string $1) }
| AND LPAREN prop COMMA prop RPAREN { Coq_prop_and ($3, $5) }
| OR LPAREN prop COMMA prop RPAREN { Coq_prop_or ($3, $5) }
| IMP LPAREN prop COMMA prop RPAREN { Coq_prop_imp ($3, $5) }
;

entry:
  LBRACKET derivation RBRACKET { Coq_entry_derivation $2 }
| LBRACKET separated_list(COMMA, entry) RBRACKET { Coq_entry_box $2 }
;

derivation:
  INT COMMA prop COMMA reason { Coq_derivation_deriv ($1, $3, $5) }
;

reason:
  ASSUMPTION { Coq_reason_assumption }
| justification { Coq_reason_justification $1 }
;

justification:
  PREMISE { Coq_justification_premise }
| LEM { Coq_justification_lem }
| COPY LPAREN INT RPAREN { Coq_justification_copy $3 }
| ANDINT LPAREN INT COMMA INT RPAREN { Coq_justification_andi ($3, $5) }
| ANDEL1 LPAREN INT RPAREN { Coq_justification_ande1 $3 }
| ANDEL2 LPAREN INT RPAREN { Coq_justification_ande2 $3 }
| ORINT1 LPAREN INT RPAREN { Coq_justification_ori1 $3 }
| ORINT2 LPAREN INT RPAREN { Coq_justification_ori2 $3 }
| IMPEL LPAREN INT COMMA INT RPAREN { Coq_justification_impe ($3, $5) }
| NEGEL LPAREN INT COMMA INT RPAREN { Coq_justification_nege ($3, $5) }
| CONTEL LPAREN INT RPAREN { Coq_justification_conte $3 }
| NEGNEGINT LPAREN INT RPAREN { Coq_justification_negnegi $3 }
| NEGNEGEL INT { Coq_justification_negnege $2 }
| MT LPAREN INT COMMA INT RPAREN { Coq_justification_mt ($3, $5) }
| IMPINT LPAREN INT COMMA INT RPAREN { Coq_justification_impi ($3, $5) }
| NEGINT LPAREN INT COMMA INT RPAREN { Coq_justification_negi ($3, $5) }
| OREL LPAREN INT COMMA INT COMMA INT COMMA INT COMMA INT RPAREN { Coq_justification_ore ($3, $5, $7, $9, $11) }
| PBC LPAREN INT COMMA INT RPAREN { Coq_justification_pbc ($3, $5) }
;
