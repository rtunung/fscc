module fscc.C

open FsToolkit.ErrorHandling
open Lexer

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
    | Conditional of condition: Expression * Expression * Expression

type Declaration = Identifier * Expression option

type Statement =
    | Return of Expression
    | Expression of Expression
    | If of condition: Expression  * Statement * Statement option
    | Goto of Identifier
    | Label of Identifier * Statement
    | Compound of Block
    
    // Created during the parsing phase
    | DummyBreak
    | DummyContinue
    | DummyWhile of condition: Expression * body: Statement
    | DummyDoWhile of  body: Statement * condition: Expression
    | DummyFor of ForInit * condition: Expression option * post: Expression option * body: Statement 
    
    // Created from dummy statements in the semantic analysis stage
    | LoopBreak of loopLabel: Identifier
    | Continue of loopLabel: Identifier
    | While of condition: Expression * body: Statement * loopLabel: Identifier
    | DoWhile of  body: Statement * condition: Expression * loopLabel: Identifier
    | For of init: ForInit * condition: Expression option * post: Expression option * body: Statement * loopLabel: Identifier 
    
    // Created during the parsing phase
    | DummySwitch of argument: Expression * body: Statement
    | DummyCase of case: Expression * body: Statement
    | DummyDefault of body: Statement
    
    // Created from dummy statements in the semantic analysis stage
    | Switch of argument: Expression * body: Statement * cases: (Identifier * Expression) list * defaultCase: Identifier option * label: Identifier
    | Case of label: Identifier * body: Statement
    | Default of label: Identifier * body: Statement
    | SwitchBreak of label: Identifier
    
    | Null

and ForInit =
    | InitDeclaration of Declaration
    | InitExpression of Expression option

and BlockItem =
    | Statement of Statement
    | Declaration of Declaration

and Block = BlockItem list

type FunctionDefinition =
    Function of Identifier * Block

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

let parseOptionalExpression tokens =
    let result = parseExpression tokens
    match result with
    | Error _ -> None, tokens
    | Ok (expr, rest) -> Some expr, rest

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
    | BraceOpen :: _ -> result {
        let! block, rest = parseBlock tokens
        return Compound block, rest
        }
    | ContinueKey :: rest -> result {
        let! rest = expectToken Semicolon rest
        return DummyContinue, rest
        }
    | BreakKey :: rest -> result {
        let! rest = expectToken Semicolon rest
        return DummyBreak, rest
        }
    | WhileKey :: rest -> result {
        let! rest = expectToken ParenOpen rest
        let! condition, rest = parseExpression rest
        let! rest = expectToken ParenClose rest
        let! body, rest = parseStatement rest
        return DummyWhile (condition, body), rest
        }
    | DoKey :: rest -> result {
        let! body, rest = parseStatement rest
        let! rest = expectToken WhileKey rest
        let! rest = expectToken ParenOpen rest
        let! condition, rest = parseExpression rest
        let! rest = expectToken ParenClose rest
        let! rest = expectToken Semicolon rest
        return DummyDoWhile (body, condition), rest
        }
    | ForKey :: rest -> result {
        let! rest = expectToken ParenOpen rest
        let! init, rest = parseForInit rest
        let conditional, rest = parseOptionalExpression rest
        let! rest = expectToken Semicolon rest
        let post, rest = parseOptionalExpression rest
        let! rest = expectToken ParenClose rest
        let! body, rest = parseStatement rest
        return DummyFor (init, conditional, post, body), rest
        }
    | CaseKey :: rest -> result {
        let! expr, rest = parseExpression rest
        let! rest = expectToken Colon rest
        let! body, rest = parseStatement rest
        return DummyCase (expr, body), rest
        }
    | DefaultKey :: Colon :: rest -> result {
        let! body, rest = parseStatement rest
        return DummyDefault body, rest
        } 
    | SwitchKey :: rest -> result {
        let! rest = expectToken ParenOpen rest
        let! argument, rest = parseExpression rest
        let! rest = expectToken ParenClose rest
        let! body, rest = parseStatement rest
        return DummySwitch (argument, body), rest
        }
    | _ :: _ -> result {
        let! expr, rest = parseExpression tokens
        let! rest = expectToken Semicolon rest
        return Expression expr, rest
        }
    | [] -> Error <| suddenEOF

and parseBlockItem tokens =
    match tokens with
    // Declarations
    | IntKey :: _ -> result {
        let! declaration, rest = parseDeclaration tokens
        return Declaration declaration, rest
        }
    // Statements
    | _ :: _ ->
        parseStatement tokens
        |> Result.map (fun (x, rest) -> (Statement x, rest))
    | [] -> Error <| suddenEOF

and parseBlock tokens =
        let rec loop tokens acc =
            match tokens with
            | BraceClose :: rest -> Ok (acc, rest)
            | _ :: _ ->
                let result = parseBlockItem tokens
                match result with
                | Error error -> Error error
                | Ok (item, rest) -> loop rest (acc @ [item])
            | [] -> Error <| suddenEOF
            
        result {
            let! rest = expectToken BraceOpen tokens
            let! result, rest = loop rest []
            return (result:Block), rest
        }
and parseDeclaration tokens =
    match tokens with
    // Declarations
    | IntKey :: Identifier ident :: Lexer.Equal :: rest -> result {
        let! expr, rest = parseExpression rest
        let! rest = expectToken Semicolon rest
        return ((Identifier ident, Some expr):Declaration), rest
        }
    | IntKey :: Identifier ident :: rest -> result {
        let! rest = expectToken Semicolon rest
        return (Identifier ident, None), rest
        }
    | unexpectedToken :: _ -> Error <| Message $"Expected Declaration, got {unexpectedToken}"
    | [] -> Error suddenEOF
        
and parseForInit tokens =
    match tokens with
    | IntKey :: _ -> result {
        let! declaration, rest = parseDeclaration tokens
        return InitDeclaration declaration, rest
        }
    | Semicolon :: rest -> Ok (InitExpression None, rest)
    | _ :: _ -> result {
        let! expression, rest = parseExpression tokens
        let! rest = expectToken Semicolon rest
        return InitExpression (Some expression), rest
        }
    | [] -> Error suddenEOF

let parseFunction tokens =
    result {
        let! rest = expectToken IntKey tokens
        let! identifier, rest = parseIdentifier rest
        let! rest = expectToken ParenOpen rest
        let! rest = expectToken VoidKey rest
        let! rest = expectToken ParenClose rest
        let! block, rest = parseBlock rest
        return Function (identifier, block), rest
    }

let parseProgram tokens : Result<Program, ParserError> =
    let prog, nextTokens =
        match parseFunction tokens with
        | Error error -> Error error, tokens
        | Ok (func, nextTokens) -> Ok (Program func), nextTokens
    if (List.isEmpty nextTokens) || (Result.isError prog) then prog
    else Error <| Message "Unexpected tokens after the end of program"
