{
open Prolog_parser
exception Error of string
}

rule token = parse
| [' ' '\t' '\n' '\r']+
    { token lexbuf }
| ','
    { COMMA }
| "neg"
    { NEG }
| "and"
    { AND }
| "or"
    { OR }
| "imp"
    { IMP }
| '.'
    { PERIOD }
| ['0'-'9']+ as i
    { INT (int_of_string i) }
| "cont"
    { CONT }
| "assumption"
    { ASSUMPTION }
| "premise"
    { PREMISE }
| "lem"
    { LEM }
| "copy" 
    { COPY }
| "andint"
    { ANDINT }
| "andel1"
    { ANDEL1 }
| "andel2"
    { ANDEL2 }
| "orint1"
    { ORINT1 }
| "orint2"
    { ORINT2 }
| "impel"
    { IMPEL }
| "negel"
    { NEGEL }
| "contel"
    { CONTEL }
| "negnegint"
    { NEGNEGINT }
| "negnegel"
    { NEGNEGEL }
| "mt"
    { MT }
| "impint"
    { IMPINT }
| "negint"
    { NEGINT }
| "orel"
    { OREL }
| "pbc"
    { PBC }
| ['a'-'z']+ as id
    { IDENT id }
| '('
    { LPAREN }
| ')'
    { RPAREN }
| '['
    { LBRACKET }
| ']'
    { RBRACKET }
| eof
    { EOF }
| _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }
