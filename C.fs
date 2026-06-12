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
    | Assignment of lvalue: Expression * rvalue: Expression
    | Unary of UnaryOperator * Expression
    | Binary of BinaryOperator * left: Expression * right: Expression
    | Conditional of condition: Expression * Expression * Expression
    | FunctionCall of Identifier * args: Expression list

type StorageClass =
    | Static
    | Extern

type Declaration =
    | VariableDecl of VariableDeclaration
    | FunctionDecl of FunctionDeclaration
    
and VariableDeclaration =
    Variable of Identifier * Expression option * StorageClass option

and Statement =
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
    | Switch of argument: Expression * body: Statement * cases: (Identifier * Expression) Set * defaultCase: Identifier option * label: Identifier
    | Case of label: Identifier * body: Statement
    | Default of label: Identifier * body: Statement
    | SwitchBreak of label: Identifier
    
    | Null

and ForInit =
    | InitDeclaration of VariableDeclaration
    | InitExpression of Expression option

and BlockItem =
    | Statement of Statement
    | Declaration of Declaration

and Block = BlockItem list

and FunctionDeclaration =
    Function of Identifier * parameters: Identifier list * body: Block option * StorageClass option

type Program = Program of Declaration list

type Type =
    | Int
    | FunType of paramCount: int

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
    
    | PlusEqual | MinusEqual | StarEqual | SlashEqual
    | PercentageEqual | AmpersandEqual | PipeEqual | CaretEqual
    | ShiftLeftEqual | ShiftRightEqual -> 1

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

let parseSpecifiers tokens =
    let parseSpecifier tokens =
        match tokens with
        | (IntKey as tok) :: rest
        | (StaticKey as tok) :: rest
        | (ExternKey as tok) :: rest -> Ok (tok, rest)
        | other :: _ -> Error <| Message $"Expected specifier token, got {other}"
        | [] -> Error suddenEOF
    
    let rec loop acc tokens =
        let result = parseSpecifier tokens
        match result with
        | Error err ->
            if List.isEmpty acc then Error err else Ok (acc, tokens)
        | Ok (specifier, rest) -> loop (acc @ [specifier]) rest
        
    loop [] tokens

let getStorageClassToken token =
    match token with
    | ExternKey -> Extern
    | StaticKey -> Static
    | _ -> failwith "Token is not a storage class specifier! This should not happen, internal compiler error!"

let parseTypeAndStorageClass specifierList =
    let isTypeSpecifier speci = speci = IntKey
    let types, storageClasses = List.partition isTypeSpecifier specifierList
    
    let thisType = if List.length types = 1
                   then Ok <| List.head types
                   else Error <| Message "More than one type was specified!"
    
    let thisStorageClass = if List.length storageClasses = 1
                           then Some (getStorageClassToken (List.head storageClasses))
                           else None
    
    result {
        let! myType = thisType
        return (myType, thisStorageClass)
    }

let isCompoundAssignment token =
    let allCompoundAssignments = [PlusEqual; MinusEqual; StarEqual; SlashEqual; PercentageEqual; AmpersandEqual; PipeEqual
                                  CaretEqual; ShiftLeftEqual; ShiftRightEqual]
    List.contains token allCompoundAssignments

let getOperatorFromCompoundAssignment token =
    match token with
    | PlusEqual -> Plus
    | MinusEqual -> Minus
    | StarEqual -> Multiply
    | SlashEqual -> Divide
    | PercentageEqual -> Remainder
    | AmpersandEqual -> BitwiseAnd
    | PipeEqual -> BitwiseOr
    | CaretEqual -> BitwiseXor
    | ShiftLeftEqual -> ShiftLeft
    | ShiftRightEqual -> ShiftRight
    | _ -> failwith $"Token '{token}' is not a compound assignment operator. This should not happen."

let rec parseFactor tokens =
    let factor =
        match tokens with
        // Constants
        | Lexer.Constant value :: rest -> Ok (Constant value, rest)
        // Function calls
        | Lexer.Identifier funcName :: ParenOpen :: ParenClose :: rest -> Ok (FunctionCall (funcName, []), rest)
        | Lexer.Identifier funcName :: ParenOpen :: rest -> result {
            let! args, rest = parseArgumentList rest []
            let! rest = expectToken ParenClose rest
            return FunctionCall (funcName, args), rest
            }
        // Variables
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
                | Some compoundToken when isCompoundAssignment compoundToken ->
                    let operator = getOperatorFromCompoundAssignment compoundToken
                    let rest = List.tail tokens
                    let! right, rest = parseExpressionPrecedence rest nextPrecedence
                    return Assignment (left, Binary (operator, left, right)), rest
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

and parseArgumentList tokens acc =
    let resultExpression = parseExpression tokens
    match resultExpression with
    | Error error -> Error error
    | Ok (expr, rest) ->
        match rest with
        | Comma :: rest -> parseArgumentList rest (acc @ [expr])
        | _ -> Ok (acc @ [expr], rest)

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
    | IntKey :: _
    | StaticKey :: _
    | ExternKey :: _ -> result {
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
        
and parseForInit tokens =
    match tokens with
    | IntKey :: _ -> result {
        let! declaration, rest = parseDeclaration tokens
        match declaration with
        | VariableDecl varDecl -> return InitDeclaration varDecl, rest
        | FunctionDecl _ -> return! Error <| Message "Function declaration instead of variable declaration inside for-header"
        }
    | Semicolon :: rest -> Ok (InitExpression None, rest)
    | _ :: _ -> result {
        let! expression, rest = parseExpression tokens
        let! rest = expectToken Semicolon rest
        return InitExpression (Some expression), rest
        }
    | [] -> Error suddenEOF

and parseParameterList tokens =
    let rec loop tokens acc =
        match tokens with
        | IntKey :: Lexer.Identifier name :: Comma :: rest ->
            loop rest (acc @ [Identifier name])
        | IntKey :: Lexer.Identifier name :: rest ->
            Ok (acc @ [Identifier name], rest)
        | unexpected :: _ -> Error <| Message $"Unexpected token {unexpected} in parameter list declaration"
        | [] -> Error suddenEOF

    match tokens with
    | VoidKey :: rest -> Ok ([], rest)
    | IntKey :: _ -> loop tokens []
    | unexpected :: _ -> Error <| Message $"Unexpected token {unexpected} in parameter list declaration"
    | [] -> Error suddenEOF

and parseDeclaration tokens =
    let parseOptionalBody tokens =
        match tokens with
        | Semicolon :: rest -> Ok (None, rest)
        | _ -> result {
            let! block, rest = parseBlock tokens
            return Some block, rest
            }
    
    result {
        let! specifiers, rest = parseSpecifiers tokens
        let! thisType(*Currently only int so unused*), storageClass = parseTypeAndStorageClass specifiers
        let! name, rest = parseIdentifier rest
        
        match rest with
        | Lexer.Equal :: rest ->
            let! expression, rest = parseExpression rest
            let! rest = expectToken Semicolon rest
            return VariableDecl <| Variable (name, Some expression, storageClass), rest
        | Semicolon :: rest -> return VariableDecl <| Variable (name, None, storageClass), rest
        | ParenOpen :: rest ->
            let! parameters, rest = parseParameterList rest
            let! rest = expectToken ParenClose rest
            let! body, rest = parseOptionalBody rest
            return FunctionDecl <| Function (name, parameters, body, storageClass), rest
        | other :: _ -> return! Error <| Message $"Unexpected token {other} found in Declaration"
        | [] -> return! Error suddenEOF
    }

let parseProgram tokens : Result<Program, ParserError> =
    
    let rec parseDeclarations tokens acc =
        match tokens with
        | [] -> Ok acc
        | _ ->
            let decl = parseDeclaration tokens
            match decl with
            | Error error -> Error error
            | Ok (func, rest) -> parseDeclarations rest (acc @ [func])
    
    result {
        let! functions = parseDeclarations tokens []
        return Program functions
    }
    