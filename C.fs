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

type Statement =
    | Return of Expression
    | Expression of Expression
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
        | Lexer.Increment :: rest -> result {
            let! exp, restTokens = parseFactor rest
            return Unary (PrefixIncrement, exp), restTokens
            }
        | Lexer.Decrement :: rest -> result {
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
            let res =
                if peekToken tokens = Some Lexer.Equal then
                    result {
                        let rest = List.tail tokens
                        let! right, rest = parseExpressionPrecedence rest nextPrecedence
                        return Assignment (left, right), rest
                        }
                    else
                        result {
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

let parseStatement tokens =
    match tokens with
    | ReturnKey :: rest -> result {
        let! expr, rest = parseExpression rest
        let! rest = expectToken Semicolon rest
        return Return expr, rest
        }
    | Semicolon :: rest -> Ok (Null, rest)
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

// Semantic Analysis

let isIncrementDecrement op =
    match op with
    | PostfixDecrement
    | PrefixDecrement
    | PostfixIncrement
    | PrefixIncrement -> true
    | _ -> false

let rec resolveExpression expr (variableMap:Map<Identifier, Identifier>) =
    match expr with
    | Assignment (Var left, right) -> result {
        let! left = resolveExpression (Var left) variableMap
        let! right = resolveExpression right variableMap
        return Assignment (left, right)
        }
    | Assignment (invalid, _) -> Error <| Message $"Invalid lvalue {invalid}"
    | Var name when Map.containsKey name variableMap ->
        let uniqueName = Map.find name variableMap
        Ok (Var uniqueName)
    | Var undeclared -> Error <| Message $"Variable {undeclared} is undeclared"
    | Constant _ -> Ok expr
    | Unary (inc, Var a) when isIncrementDecrement inc -> result {
        let! expr = resolveExpression (Var a) variableMap
        return Unary (inc, expr)
        }
    | Unary (inc, invalid) when isIncrementDecrement inc -> Error <| Message $"Invalid lvalue {invalid} for operator {inc}"
    | Unary(operator, expression) -> result {
        let! expression = resolveExpression expression variableMap
        return Unary(operator, expression)
        }
    | Binary(operator, left, right) -> result {
        let! left = resolveExpression left variableMap
        let! right = resolveExpression right variableMap
        return Binary(operator, left, right)
        }

let resolveDeclaration (ident, expr) (variableMap:Map<Identifier,Identifier>) =
    if Map.containsKey ident variableMap then
        Error <| Message $"Duplicate variable declaration of {ident}"
    else
        let uniqueName = Identifier (getTemporaryName ())
        let variableMap = Map.add ident uniqueName variableMap

        let expr = Option.map (fun x -> resolveExpression x variableMap) expr
        match expr with
        | None -> Ok (Declaration (uniqueName, None), variableMap)
        | Some (Error error) -> Error error
        | Some (Ok expr) -> Ok (Declaration (uniqueName, Some expr), variableMap)

let resolveBlockItem item variableMap =
    match item with
    | Declaration declaration -> resolveDeclaration declaration variableMap
    | Statement Null -> Ok (Statement Null, variableMap)
    | Statement (Return expr) -> result {
        let! expr = resolveExpression expr variableMap
        return Statement (Return expr), variableMap
        }
    | Statement (Expression expr) -> result {
        let! expr = resolveExpression expr variableMap
        return Statement (Expression expr), variableMap
    }
    
let resolveBlockItems items variableMap =
    let rec loop items variableMap acc =
        match items with
        | [] -> Ok acc
        | item :: rest ->
            let resolvedItem = resolveBlockItem item variableMap
            match resolvedItem with
            | Error error -> Error error
            | Ok (newItem, variableMap) -> loop rest variableMap (acc @ [newItem])
    
    loop items variableMap []
    
let resolveFunction (Function(funcName, blockItems)) variableMap = result {
    let! resolvedItem = resolveBlockItems blockItems variableMap
    return Function (funcName, resolvedItem)
    }

let semanticAnalysis (Program func) =
    let newMap = Map.empty
    result {
        let! resolvedFunc = resolveFunction func newMap
        return Program resolvedFunc
    }