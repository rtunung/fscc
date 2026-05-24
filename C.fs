module fscc.C

open FsToolkit.ErrorHandling
open Lexer
open fscc.Misc

// <program> ::= <function>
// <function> ::= "int" <identifier> "(" "void" ")" "{" { <block-item> } "}"
// <block-item> ::= <statement> | <declaration>
// <declaration> ::= "int" <identifier> [ "=" <exp> ] ";"
// <statement> ::= "return" <exp> ";" | <exp> ";" | ";"
// <exp> ::= <factor> | <exp> <binop> <exp>
// <factor> ::= <int> | <identifier> | <unop> <factor> | "(" <exp> ")" | <exp> ( "--" | "++" )
// <unop> ::= "-" | "~" | "!" | "++" | "--"
// <binop> ::= "-" | "+" | "*" | "/" | "%" | "&&" | "||"
//           | "==" | "!=" | "<" | "<=" | ">" | ">=" | "="
//           | "^" | "|" | "&"
// <identifier> ::= ? An identifier token ?
// <int> ::= ? A constant token ?

type Identifier = string

type UnaryOperator =
    | Complement
    | Negate
    | Not
    | PrefixIncrement
    | PrefixDecrement
    | PostfixIncrement
    | PostfixDecrement

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
    | Var of Identifier
    | Assignment of Expression * Expression
    | Unary of UnaryOperator * Expression
    | Binary of BinaryOperator * Expression * Expression
    | Conditional of Expression * Expression * Expression

type Statement =
    | Return of Expression
    | Expression of Expression
    | If of Expression  * Statement * Statement option
    | Goto of Identifier
    | Label of Identifier * Statement
    | Null

type Declaration = Identifier * Expression option

type BlockItem =
    | Statement of Statement
    | Declaration of Declaration

type FunctionDefinition =
    Function of Identifier * BlockItem list

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

let peekToken tokens =
    match tokens with
    | tok :: _ -> Some tok
    | [] -> None

let parseIdentifier tokens =
    match tokens with
    | Lexer.Identifier value :: rest -> Ok (Identifier value, rest)
    | token :: _ -> Error <| Message $"Expected identifier got '{token}'"
    | [] -> Error suddenEOF

let getBinaryPrecedence token =
    match token with
    | Slash -> 55
    | Percentage -> 55
    | Asterisk -> 55
    
    | Lexer.Minus -> 50
    | Lexer.Plus -> 50

    | Lexer.ShiftLeft -> 45
    | Lexer.ShiftRight -> 45
    
    | Less -> 40
    | LessEqual -> 40
    | Greater -> 40
    | GreaterEqual -> 40
    
    | DoubleEqual -> 35
    | ExclamationEqual -> 35
    
    | Ampersand -> 30
    | Caret -> 25
    | Pipe -> 20

    | DoubleAmpersand -> 10
    | DoublePipe -> 5
    | QuestionMark -> 3
    | Lexer.Equal -> 1
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
    | Greater :: rest -> Ok (GreaterThan, rest)
    | GreaterEqual :: rest -> Ok (GreaterOrEqual, rest)
    | Less :: rest -> Ok (LessThan, rest)
    | LessEqual :: rest -> Ok (LessOrEqual, rest)
    | DoubleEqual :: rest -> Ok (Equal, rest)
    | ExclamationEqual :: rest -> Ok (NotEqual, rest)

    | other :: _ -> Error <| Message $"Expected binary operation, got {other}"
    | [] -> Error <| suddenEOF

let rec parseFactor tokens =
    let factor =
        match tokens with
        | Lexer.Constant value :: rest -> Ok (Constant value, rest)
        | Lexer.Identifier ident :: rest -> Ok (Var ident, rest)
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
        | Increment :: rest -> result {
            let! exp, restTokens = parseFactor rest
            return Unary (PrefixIncrement, exp), restTokens
            }
        | Decrement :: rest -> result {
            let! exp, restTokens = parseFactor rest
            return Unary (PrefixDecrement, exp), restTokens
            }
        // Parse Expression inside parentheses
        | ParenOpen :: rest -> result {
            let! exp, restTokens = parseExpression rest
            let! restTokens = expectToken ParenClose restTokens
            return exp, restTokens
            }
        | other :: _ -> Error <| Message $"Malformed expression: found '{other}' instead of an correct expression token"
        | [] -> Error suddenEOF
    
    // Handle Postfix operators
    // Maybe move this to parseExpressionPrecedence? Will need to do some testing
    match factor with
    | Error error -> Error error
    | Ok (expr, restTokens) ->
        match restTokens with
        | Increment :: rest -> Ok (Unary (PostfixIncrement, expr), rest)
        | Decrement :: rest -> Ok (Unary (PostfixDecrement, expr), rest)
        | _ -> Ok (expr, restTokens)
    
and parseExpressionPrecedence tokens minPrecedence =
    let rec loop left tokens =
        let nextPrecedence = getNextPrecedence tokens
        if nextPrecedence >= minPrecedence then
            let res = result {
                match peekToken tokens with
                | Some Lexer.Equal ->
                    let rest = List.tail tokens
                    let! right, rest = parseExpressionPrecedence rest nextPrecedence
                    return Assignment (left, right), rest
                | Some QuestionMark ->
                    let! middle, rest = parseConditionalMiddle tokens
                    let! right, rest = parseExpressionPrecedence rest nextPrecedence
                    return Conditional (left, middle, right), rest
                | _ ->
                    let! operator, rest = parseBinaryOperator tokens
                    let! right, rest = parseExpressionPrecedence rest (nextPrecedence + 1)
                    let left = Binary (operator, left, right)
                    return left, rest
                }
            match res with
            | Error _  -> res
            | Ok (left, rest) -> loop left rest
        else
            Ok (left, tokens)
            
    result {
        let! left, rest = parseFactor tokens
        let! left, rest = loop left rest
        return left, rest
    }
    
and parseExpression tokens = parseExpressionPrecedence tokens 0

and parseConditionalMiddle tokens = result {
    let! rest = expectToken QuestionMark tokens
    let! expr, rest = parseExpression rest
    let! rest = expectToken Colon rest
    return expr, rest
}

let rec parseStatement tokens =
    match tokens with
    | ReturnKey :: rest -> result {
        let! expr, rest = parseExpression rest
        let! rest = expectToken Semicolon rest
        return Return expr, rest
        }
    | Semicolon :: rest -> Ok (Null, rest)
    | IfKey :: rest -> result {
        let! rest = expectToken ParenOpen rest
        let! cond, rest = parseExpression rest
        let! rest = expectToken ParenClose rest
        let! ifBody, rest = parseStatement rest
        match rest with
        | ElseKey :: rest ->
            let! elseBody, rest = parseStatement rest
            return If (cond, ifBody, Some elseBody), rest
        | _ -> return If (cond, ifBody, None), rest
        }
    | Lexer.Identifier labelName :: Colon :: rest -> result {
        let! statement, rest = parseStatement rest
        return Label (labelName, statement), rest
        }
    | GotoKey :: Lexer.Identifier labelName :: Semicolon :: rest ->
        Ok (Goto labelName, rest)
    | _ :: _ -> result {
        let! expr, rest = parseExpression tokens
        let! rest = expectToken Semicolon rest
        return Expression expr, rest
        }
    | [] -> Error <| suddenEOF

let parseBlockItem tokens =
    match tokens with
    // Declarations
    | IntKey :: Identifier ident :: Lexer.Equal :: rest -> result {
        let! expr, rest = parseExpression rest
        let! rest = expectToken Semicolon rest
        return Declaration (Identifier ident, Some expr), rest
        }
    | IntKey :: Identifier ident :: rest -> result {
        let! rest = expectToken Semicolon rest
        return Declaration (Identifier ident, None), rest
        }
    // Statements
    | _ :: _ ->
        parseStatement tokens
        |> Result.map (fun (x, rest) -> (Statement x, rest))
    | [] -> Error <| suddenEOF

let parseFunction tokens =
    let rec parseBlockItems tokens acc =
        match tokens with
        | BraceClose :: _ -> Ok (acc, tokens)
        | _ :: _ ->
            let result = parseBlockItem tokens
            match result with
            | Error error -> Error error
            | Ok (item, rest) -> parseBlockItems rest (acc @ [item])
        | [] -> Error <| suddenEOF

    result {
        let! rest = expectToken IntKey tokens
        let! identifier, rest = parseIdentifier rest
        let! rest = expectToken ParenOpen rest
        let! rest = expectToken VoidKey rest
        let! rest = expectToken ParenClose rest
        let! rest = expectToken BraceOpen rest
        let! blockItems, rest = parseBlockItems rest []
        let! rest = expectToken BraceClose rest
        return Function (identifier, blockItems), rest
    }

let parseProgram tokens : Result<Program, ParserError> =
    let prog, nextTokens =
        match parseFunction tokens with
        | Error error -> Error error, tokens
        | Ok (func, nextTokens) -> Ok (Program func), nextTokens
    if (List.isEmpty nextTokens) || (Result.isError prog) then prog
    else Error <| Message "Unexpected tokens after the end of program"
