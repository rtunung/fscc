module fscc.C

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
    | Not

type BinaryOperator =
    | Plus
    | Minus
    | Multiply
    | Divide
    | Remainder
    | BitwiseOr
    | BitwiseAnd
    | BitwiseXor
    | ShiftLeft
    | ShiftRight
    | And
    | Or
    | Equal
    | NotEqual
    | GreaterThan
    | LessThan
    | GreaterOrEqual
    | LessOrEqual

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

let getBinaryPrecedence token =
    match token with
    | Lexer.Minus -> 45
    | Lexer.Plus -> 45
    | Slash -> 55
    | Percentage -> 55
    | Asterisk -> 50
    | Lexer.ShiftLeft -> 40
    | Lexer.ShiftRight -> 40
    | Ampersand -> 38
    | Caret -> 38
    | Pipe -> 38
    | Lexer.Less -> 35
    | Lexer.LessEqual -> 35
    | Lexer.Greater -> 35
    | Lexer.GreaterEqual -> 35
    | DoubleEqual -> 30
    | ExclamationEqual -> 30
    | DoubleAmpersand -> 10
    | DoublePipe -> 5
    | _ -> -100

let getNextPrecedence tokens =
    match tokens with
    | operator :: _ -> getBinaryPrecedence operator
    | _ -> -100
    
let parseBinaryOperator tokens =
    match tokens with
    | Lexer.Plus :: rest -> Ok (Plus, rest)
    | Lexer.Minus :: rest -> Ok (Minus, rest )
    | Slash :: rest -> Ok (Divide, rest)
    | Asterisk :: rest -> Ok (Multiply, rest)
    | Percentage :: rest -> Ok (Remainder, rest)
    | Pipe :: rest -> Ok (BitwiseOr, rest)
    | Ampersand :: rest -> Ok (BitwiseAnd, rest)
    | Caret :: rest -> Ok (BitwiseXor, rest)
    | Lexer.ShiftLeft :: rest -> Ok (ShiftLeft, rest)
    | Lexer.ShiftRight :: rest -> Ok (ShiftRight, rest) 
    | DoubleAmpersand :: rest -> Ok (And, rest)
    | DoublePipe :: rest -> Ok (Or, rest)
    | Lexer.Greater :: rest -> Ok (GreaterThan, rest)
    | Lexer.GreaterEqual :: rest -> Ok (GreaterOrEqual, rest)
    | Lexer.Less :: rest -> Ok (LessThan, rest)
    | Lexer.LessEqual :: rest -> Ok (LessOrEqual, rest)
    | DoubleEqual :: rest -> Ok (Equal, rest)
    | ExclamationEqual :: rest -> Ok (NotEqual, rest)

    | other :: _ -> Error <| Message $"Expected binary operation, got {other}"
    | [] -> Error <| suddenEOF

let rec parseFactor tokens =
    match tokens with
    | Lexer.Constant value :: rest -> Ok (Constant value, rest)
    // Parsing Unary Operators
    | Tilde :: rest -> result {
        let! exp, restTokens = parseFactor rest
        return Unary (Complement, exp), restTokens
        }
    | Lexer.Minus :: rest -> result {
        let! exp, restTokens = parseFactor rest
        return Unary (Negate, exp), restTokens
        }
    | Exclamation :: rest -> result {
        let! exp, restTokens = parseFactor rest
        return Unary (Not, exp), restTokens
        }
    // Parse Expression inside parentheses
    | ParenOpen :: rest -> result {
        let! exp, restTokens = parseExpression rest
        let! restTokens = expectToken ParenClose restTokens
        return exp, restTokens
        }
    | other :: _ -> Error <| Message $"Malformed expression: found '{other}' instead of an correct expression token"
    | [] -> Error suddenEOF
    
and parseExpressionPrecedence tokens minPrecedence =
    let rec loop left toks =
        let nextPrecedence = getNextPrecedence toks
        if nextPrecedence >= minPrecedence then
            let res = result {
                let! operator, restTokens = parseBinaryOperator toks
                let! right, restTokens = parseExpressionPrecedence restTokens (nextPrecedence + 1)
                let left = Binary (operator, left, right)
                return left, restTokens
                }
            match res with
            | Error _  -> res
            | Ok (left, restTokens) -> loop left restTokens
        else
            Ok (left, toks)
            
    result {
        let! left, restTokens = parseFactor tokens
        let! left, restTokens = loop left restTokens
        return left, restTokens
    }
    
and parseExpression tokens = parseExpressionPrecedence tokens 0

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
