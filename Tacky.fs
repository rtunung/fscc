module fscc.Tacky

open fscc.C
open fscc.SemanticAnalysis
open Misc

type Identifier = string

type UnaryOperator =
    | Complement
    | Negate
    | Not
    
type BinaryOperator =
    | Minus
    | Plus
    | Divide
    | Multiply
    | Remainder
    | BitwiseOr
    | BitwiseAnd
    | BitwiseXor
    | ShiftLeft
    | ShiftRight
    | LessThan
    | GreaterThan
    | LessOrEqual
    | GreaterOrEqual
    | Equal
    | NotEqual
    
type Value =
    | Constant of int
    | Var of Identifier
    
type Instruction =
    | Return of Value
    | Unary of {| op : UnaryOperator; src : Value; dst : Value |}
    | Binary of {| op: BinaryOperator; srcLeft : Value; srcRight : Value; dst : Value |}
    | Copy of {| src : Value; dst : Value |}
    | Jump of Identifier
    | JumpIfZero of {| condition : Value; target : Identifier|}
    | JumpIfNotZero of {| condition : Value; target : Identifier|}
    | Label of Identifier
    | FunctionCall of name: Identifier * args: Value list * dst: Value
    
type TopLevel =
    | Function of name: Identifier * globl: bool * parameters: Identifier list * instructions: Instruction list
    | StaticVariable of name: Identifier * globl: bool * init: int

type Program =
    Program of TopLevel list
    
let makeJumpZero src label =
    JumpIfZero {| condition = src; target = label |}

let makeJumpNotZero src label =
    JumpIfNotZero {| condition = src; target = label |}

let makeCopy src dst =
    Copy {| src = src; dst = dst; |}

    
let convertUnary unary =
    match unary with
    | C.Complement -> Complement
    | C.Negate -> Negate
    | C.Not -> Not
    | PrefixIncrement
    | PrefixDecrement
    | PostfixIncrement
    | PostfixDecrement -> failwith "Cannot directly convert Increment/Decrement operators to tacky operator"

let convertBinary binary =
    match binary with
    | C.Plus -> Plus
    | C.Minus -> Minus
    | C.Multiply -> Multiply
    | C.Divide -> Divide
    | C.Remainder -> Remainder
    | C.BitwiseOr -> BitwiseOr
    | C.BitwiseAnd -> BitwiseAnd
    | C.BitwiseXor -> BitwiseXor
    | C.ShiftLeft -> ShiftLeft
    | C.ShiftRight -> ShiftRight
    | C.Equal -> Equal
    | C.NotEqual -> NotEqual
    | C.GreaterThan -> GreaterThan
    | C.LessThan -> LessThan
    | C.GreaterOrEqual -> GreaterOrEqual
    | C.LessOrEqual -> LessOrEqual
    
    | And
    | Or -> failwith "And and Or require a different conversion. This should not happen."

let varOne = Constant 1
let varZero = Constant 0
let rec emitInstruction expression=
    match expression with
    | C.Constant value -> Constant value, []
    | C.Var x -> Var x, []
    | C.Unary (PrefixIncrement, exp) ->
        let src, instructions = emitInstruction exp
        let increment = Binary {| op = Plus; dst = src; srcLeft = src; srcRight = Constant 1 |}
        src, instructions @ [increment]
    | C.Unary (PrefixDecrement, exp) ->
        let src, instructions = emitInstruction exp
        let increment = Binary {| op = Minus; dst = src; srcLeft = src; srcRight = Constant 1 |}
        src, instructions @ [increment]
    | C.Unary (PostfixIncrement, exp) ->
        let src, instructions = emitInstruction exp
        let oldValue = Var <| getTemporaryName ()
        let increment = Binary {| op = Plus; dst = src; srcLeft = src; srcRight = Constant 1 |}
        oldValue, instructions @ [makeCopy src oldValue; increment]
    | C.Unary (PostfixDecrement, exp) ->
        let src, instructions = emitInstruction exp
        let oldValue = Var <| getTemporaryName ()
        let increment = Binary {| op = Minus; dst = src; srcLeft = src; srcRight = Constant 1 |}
        oldValue, instructions @ [makeCopy src oldValue; increment]
    | C.Unary (operator, exp) ->
        let src, instructions = emitInstruction exp
        let dst = Var <| getTemporaryName ()
        let unaryInstruction = Unary {| op = convertUnary operator; src = src; dst = dst |}
        dst, instructions @ [unaryInstruction]
    | C.Binary(And, expLeft, expRight) ->
        let falseLabel = getFalseLabel ()
        let endLabel = getEndLabel ()
        let resultDst = Var <| getTemporaryName ()
        let srcLeft, leftInstructions = emitInstruction expLeft
        let nextInstructions = leftInstructions @ [makeJumpZero srcLeft falseLabel]
        let srcRight, rightInstructions = emitInstruction expRight
        let nextInstructions =
            nextInstructions @ rightInstructions @ [makeJumpZero srcRight falseLabel; makeCopy (Constant 1) resultDst; Jump endLabel
                                                    Label falseLabel; makeCopy (Constant 0) resultDst; Label endLabel]
        resultDst, nextInstructions
    | C.Binary(Or, expLeft, expRight) ->
        let trueLabel = getFalseLabel ()
        let endLabel = getEndLabel ()
        let resultDst = Var <| getTemporaryName ()
        let srcLeft, leftInstructions = emitInstruction expLeft
        let nextInstructions = leftInstructions @ [makeJumpNotZero srcLeft trueLabel]
        let srcRight, rightInstructions = emitInstruction expRight
        let nextInstructions =
            nextInstructions @ rightInstructions @ [makeJumpNotZero srcRight trueLabel; makeCopy (Constant 0) resultDst; Jump endLabel
                                                    Label trueLabel; makeCopy (Constant 1) resultDst; Label endLabel]
        resultDst, nextInstructions
    | C.Binary(operator, expLeft, expRight) ->
        let srcLeft, leftInstructions = emitInstruction expLeft
        let srcRight, rightInstructions = emitInstruction expRight
        let dst = Var <| getTemporaryName ()
        let newInstruction = Binary {| op = convertBinary operator; srcLeft = srcLeft; srcRight = srcRight; dst = dst |}
        dst, leftInstructions @ rightInstructions @ [newInstruction]
    | Assignment(C.Var ident, right) ->
        let result, instructions = emitInstruction right
        Var ident, instructions @ [makeCopy result (Var ident)]
    | Assignment(invalid, _) -> failwith $"invalid lvalue {invalid} for assignment. This shouldn't happen after the Semantic Analysis stage"
    | Conditional(cond, middle, right) ->
        let condVal, condInstructions = emitInstruction cond
        let v1, middleInstructions = emitInstruction middle
        let v2, rightInstructions = emitInstruction right
        let endLabel = getEndLabel ()
        let falseLabel = getFalseLabel ()
        let result = Var <| getTemporaryName ()
        let instructions =
            condInstructions @ [makeJumpZero condVal falseLabel] @ middleInstructions @ [makeCopy v1 result; Jump endLabel; Label falseLabel]
            @ rightInstructions @ [makeCopy v2 result; Label endLabel]
        result, instructions
    | C.FunctionCall(name, arguments) ->
        let argValues, argInstructions =
            arguments
            |> List.map emitInstruction
            |> List.unzip
            |> fun (x, y) -> x, List.concat y
        
        let dst = Var <| getTemporaryName ()    
        let instructions = argInstructions @ [FunctionCall (name, argValues, dst)]
        dst, instructions

let rec fromStatement statement =
    match statement with
    | C.Return expr ->
        let dst, instructions = emitInstruction expr
        instructions @ [Return dst]
    | Expression expr ->
        let _, instructions = emitInstruction expr
        instructions
    | If(cond, ifBody, elseOption) ->
        let condVal, condInstructions = emitInstruction cond
        let ifBodyInstructions = fromStatement ifBody
        let endLabel = getEndLabel ()
        match elseOption with
        | None ->
            condInstructions @ [makeJumpZero condVal endLabel] @ ifBodyInstructions @ [Label endLabel]
        | Some elseBody ->
            let elseLabel = getElseLabel ()
            let elseBodyInstructions = fromStatement elseBody
            condInstructions @ [makeJumpZero condVal elseLabel] @
                ifBodyInstructions @ [Jump endLabel; Label elseLabel] @ elseBodyInstructions @ [Label endLabel]
    | Null -> []
    | Goto label -> [Jump label]
    | C.Label (labelName, labelStatement) -> [Label labelName] @ fromStatement labelStatement
    | Compound block -> fromBlock block

    | LoopBreak label -> [Jump (label + ".end")]
    | Continue label -> [Jump label]
    | DoWhile (body, condition, label) ->
        let bodyInstructions = fromStatement body
        let cond, condInstructions = emitInstruction condition
        let startLabel = label + ".start"
        
        [Label startLabel] @ bodyInstructions @
        [Label label] @ condInstructions @
        [makeJumpNotZero cond startLabel; Label (label + ".end")]
        
    | While (condition, body, label) ->
        let bodyInstructions = fromStatement body
        let cond, condInstructions = emitInstruction condition
        let endLabel = label + ".end"
        
        [Label label] @ condInstructions @ [makeJumpZero cond endLabel] @
        bodyInstructions @ [Jump label; Label endLabel]
        
    | For(init, condition, post, body, label) ->
        let initInstructions =
            match init with
            | InitDeclaration declaration -> fromVariableDeclaration declaration
            | InitExpression None -> []
            | InitExpression (Some expr) -> expr |> emitInstruction |> snd
        let bodyInstruction = fromStatement body
        let cond, condInstructions =
            match condition with
            | Some cond -> emitInstruction cond
            | None -> Constant 1, []
        let postInstructions =
            match post with
            | None -> []
            | Some expr -> expr |> emitInstruction |> snd
        let endLabel = label + ".end"
        let startLabel = label + ".start"
        
        initInstructions @ [Label startLabel] @ condInstructions @ [makeJumpZero cond endLabel] @
        bodyInstruction @ [Label label] @ postInstructions @ [Jump startLabel; Label endLabel]

    | Case (label, body) -> [Label label] @ fromStatement body
    | Default (label, body) -> [Label label] @ fromStatement body
    | SwitchBreak label -> [Jump label]
    | Switch(argument, body, cases, defaultCase, label) ->
        let arg, argumentInstructions = emitInstruction argument
        let bodyInstructions = fromStatement body
        let cmpResult = Var <| getTemporaryName ()
        
        let genJumps (label, expr) =
            let value, exprInstructions = emitInstruction expr
            let comparison = Binary {| op = Equal; srcLeft = value; srcRight = arg; dst = cmpResult |}
            exprInstructions @ [comparison; makeJumpNotZero cmpResult label]
        
        let conditionalChecks =
            cases
            |> Set.toList
            |> List.collect genJumps 
        
        let defaultJump =
            match defaultCase with
            | None -> []
            | Some defaultLabel -> [Jump defaultLabel]
            
        argumentInstructions @ conditionalChecks @ defaultJump @ [Jump label] @
        bodyInstructions @ [Label label]
    
    | DummySwitch _
    | DummyCase _
    | DummyDefault _
    | DummyBreak
    | DummyContinue 
    | DummyWhile _
    | DummyDoWhile _
    | DummyFor _ -> failwith "Semantic analysis stage must be performed before TACKY generation"


and fromVariableDeclaration (Variable (ident, initValue, storageClass)) =
    if storageClass = None then
        match initValue with
        | None -> []
        | Some expr ->
            let dst, instructions = emitInstruction expr
            instructions @ [makeCopy dst (Var ident)]
    else []

and fromBlockItem blockItem =
    match blockItem with
    | Declaration (VariableDecl variable) -> fromVariableDeclaration variable
    | Declaration (FunctionDecl (C.Function (_, _, None, _))) -> []
    | Declaration (FunctionDecl (C.Function (_, _, Some _, _))) ->
        failwith "Function definition inside a block is not allowed! This should have been caught in the type checking pass!"
    | Statement statement -> fromStatement statement

and fromBlock block = List.collect fromBlockItem block

let fromFunction symbolTable (C.Function (name, parameters, body, storageClass))=
    match body with
    | None -> None
    | Some block ->
        let instructions = fromBlock block @ [Return (Constant 0)]
        let globl =
            Map.find name symbolTable
            |> _.attribute
            |> getGlobalFromAttribute
        Some <| Function (name, globl, parameters, instructions)
    
let fromTopFileDeclaration symbolTable declaration =
    match declaration with
    | VariableDecl _ -> None
    | FunctionDecl func -> fromFunction symbolTable func

let fromSymbolTable (symbolTable:SymbolTable) =
    let fromSymbolEntry (name, symbol) =
        match symbol.attribute with
        | StaticAttr (init, globl) ->
            match init with
            | Initial i -> Some (StaticVariable (name, globl, i))
            | Tentative -> Some (StaticVariable (name, globl, 0))
            | NoInitializer -> None
        | _ -> None
        
    symbolTable
    |> Map.toSeq
    |> Seq.map fromSymbolEntry
    |> Seq.toList

let fromProgram symbolTable (C.Program functions) =
    functions
    |> List.map (fromTopFileDeclaration symbolTable)
    |> (@) (fromSymbolTable symbolTable)
    |> List.choose id
    |> Program