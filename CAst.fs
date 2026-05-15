module fscc.CAst

open System.Reflection.Metadata.Ecma335
open FsToolkit.ErrorHandling
open Lexer

// <program> ::= <function>
// <function> ::= "int" <identifier> "(" "void" ")" "{" <statement> "}"
// <statement> ::= "return" <exp> ";"
// <exp> ::= <factor> | <exp> <binop> <exp>
// <factor> ::= <int> | <unop> <factor> | "(" <exp> ")"
// <unop> ::= "-" | "~"
// <binop> ::= "-" | "+" | "*" | "/" | "%"
// <identifier> ::= ? An identifier token ?
// <int> ::= ? A constant token ?

type Identifier = string

type UnaryOperator =
    | Complement
    | Negate

type BinaryOperator =
    | Plus
    | Minus
    | Multiply
    | Divide
    | Remainder

type Expression =
    | Constant of int
    | Unary of UnaryOperator * Expression
    | Binary of BinaryOperator * Expression * Expression

type Statement =
    | Return of Expression

type FunctionDefinition =
    Function of {| name : Identifier; instructions: Statement |}

type Program = Program of FunctionDefinition

type ParserError =
    | Message of string
    | LexError of LexerError

let suddenEOF = Message "Sudden end of file"

let expectToken expected tokenList =
    match tokenList with
    | token :: rest when token = expected -> Ok rest
    | token :: _ -> Error <| Message $"Expected '{expected}' got '{token}'"
    | [] -> Error suddenEOF

let parseIdentifier tokens =
    match tokens with
    | Lexer.Identifier value :: rest -> Ok (Identifier value, rest)
    | token :: _ -> Error <| Message $"Expected identifier got '{token}'"
    | [] -> Error suddenEOF



let isBinaryOperation token =
    match token with
    | Lexer.Minus -> true
    | Lexer.Plus -> true
    | Slash -> true
    | Percentage -> true
    | Asterisk -> true
    | _ -> false

let isNextBinaryOperator tokens =
    match tokens with
    | operator :: _ -> isBinaryOperation operator
    | _ -> false
    
let parseBinaryOperator tokens =
    match tokens with
    | Lexer.Plus :: rest -> Ok (Plus, rest)
    | Lexer.Minus :: rest -> Ok (Minus, rest )
    | Slash :: rest -> Ok (Divide, rest)
    | Asterisk :: rest -> Ok (Multiply, rest)
    | Percentage :: rest -> Ok (Remainder, rest)
    | other :: _ -> Error <| Message $"Expected binary operation, got {other}"

let rec parseFactor tokens =
    match tokens with
    | Lexer.Constant value :: rest -> Ok (Constant value, rest)
    | Tilde :: rest -> result {
        let! exp, restTokens = parseFactor rest
        return Unary (Complement, exp), restTokens
        }
    | Lexer.Minus :: rest -> result {
        let! exp, restTokens = parseFactor rest
        return Unary (Negate, exp), restTokens
        }
    | ParenOpen :: rest -> result {
        let! exp, restTokens = parseExpression rest
        let! restTokens = expectToken ParenClose restTokens
        return exp, restTokens
        }
    | other :: _ -> Error <| Message $"Malformed expression: found '{other}' instead of an correct expression token"
    | [] -> Error suddenEOF
and parseExpression tokens =
    let rec loop left toks =
        if isNextBinaryOperator toks then
            result {
                let! operator, restTokens = parseBinaryOperator toks
                let! right, restTokens = parseFactor restTokens
                let left = Binary (operator, left, right)
                return! (loop left restTokens)
            }
        else
            Ok (left, toks)
            
    result {
        let! left, restTokens = parseFactor tokens
        let! left, restTokens = loop left restTokens
        return left, restTokens
    }

let parseReturn tokens =
    result {
        let! t = expectToken ReturnKey tokens
        let! expression, t = parseExpression t
        let! t = expectToken Semicolon t
        return Return expression, t
    }

let parseStatement tokens =
    parseReturn tokens

let parseFunction tokens =
    result {
        let! t = expectToken IntKey tokens
        let! identifier, t = parseIdentifier t
        let! t = expectToken ParenOpen t
        let! t = expectToken VoidKey t
        let! t = expectToken ParenClose t
        let! t = expectToken BraceOpen t
        let! statement, t = parseStatement t
        let! t = expectToken BraceClose t
        return Function {| name = identifier; instructions = statement|}, t
    }

let parseProgram tokens : Result<Program, ParserError> =
    let prog, nextTokens =
        match parseFunction tokens with
        | Error error -> Error error, tokens
        | Ok (func, nextTokens) -> Ok (Program func), nextTokens
    if (List.isEmpty nextTokens) || (Result.isError prog) then prog
    else Error <| Message "Unexpected tokens after the end of program"
