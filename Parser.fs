module fscc.Parser

open FsToolkit.ErrorHandling
open Lexer

// <program> ::= <function>
// <function> ::= "int" <identifier> "(" "void" ")" "{" <statement> "}"
// <statement> ::= "return" <exp> ";"
// <exp> ::= <int>
// <identifier> ::= ? An identifier token ?
// <int> ::= ? A constant token ?

type Identifier = Identifier of string

type Expression =
    | Constant of int

type Statement =
    | Return of Expression

type FunctionDefinition =
    Function of {| name : Identifier; body : Statement |}

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

let parseConstant tokens =
    match tokens with
    | Lexer.Constant value :: rest -> Ok (Constant value, rest)
    | token :: rest -> Error <| Message $"Expected integer constant got '{token}'"
    | [] -> Error suddenEOF

let parseIdentifier tokens =
    match tokens with
    | Lexer.Identifier value :: rest -> Ok (Identifier value, rest)
    | token :: _ -> Error <| Message $"Expected identifier got '{token}'"
    | [] -> Error suddenEOF

let parseExpression tokens =
    parseConstant tokens

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
        return Function {| name = identifier; body = statement|}, t
    }

let parseProgram tokens : Result<Program, ParserError> =
    let prog, nextTokens =
        match parseFunction tokens with
        | Error error -> Error error, tokens
        | Ok (func, nextTokens) -> Ok (Program func), nextTokens
    if (List.isEmpty nextTokens) || (Result.isError prog) then prog
    else Error <| Message "Unexpected tokens after the end of program"
