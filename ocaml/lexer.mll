{
open Parser
exception Error of string
}

rule token = parse
| ','
    { COMMA }
| '~'
    { NOT }
| "/\\"
    { AND }
| "\\/"
    { OR }
| "->"
    { IMPLIES }
| "|-"
    { VDASH }
| '-'
    { DASH }
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
| "andi"
    { ANDI }
| "ande1"
    { ANDE1 }
| "ande2"
    { ANDE2 }
| "ori1"
    { ORI1 }
| "ori2"
    { ORI2 }
| "impe"
    { IMPE }
| "nege"
    { NEGE }
| "conte"
    { CONTE }
| "negnegi"
    { NEGNEGI }
| "negnege"
    { NEGNEGE }
| "mt"
    { MT }
| "impi"
    { IMPI }
| "negi"
    { NEGI }
| "ore"
    { ORE }
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
