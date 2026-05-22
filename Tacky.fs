module fscc.Tacky

open fscc.C
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
    
type FunctionDefinition =
    Function of {| name : Identifier; instructions: Instruction list |}
    
type Program =
    Program of FunctionDefinition
    
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
    | PrefixDecrement -> failwith "Cannot directly convert Increment/Decrement operators to tacky operator"

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
let rec emitInstruction expression instructions =
    match expression with
    | C.Constant value -> Constant value, instructions
    | C.Var x -> Var x, instructions
    | C.Unary (PrefixIncrement, exp) ->
        let src, nextInstructions = emitInstruction exp instructions
        let increment = Binary {| op = Plus; dst = src; srcLeft = src; srcRight = Constant 1 |}
        src, nextInstructions @ [increment]
    | C.Unary (PrefixDecrement, exp) ->
        let src, nextInstructions = emitInstruction exp instructions
        let increment = Binary {| op = Minus; dst = src; srcLeft = src; srcRight = Constant 1 |}
        src, nextInstructions @ [increment]
    | C.Unary (PostfixIncrement, exp) ->
        let src, nextInstructions = emitInstruction exp instructions
        let oldValue = Var <| getTemporaryName ()
        let increment = Binary {| op = Plus; dst = src; srcLeft = src; srcRight = Constant 1 |}
        oldValue, nextInstructions @ [makeCopy src oldValue; increment]
    | C.Unary (PostfixDecrement, exp) ->
        let src, nextInstructions = emitInstruction exp instructions
        let oldValue = Var <| getTemporaryName ()
        let increment = Binary {| op = Minus; dst = src; srcLeft = src; srcRight = Constant 1 |}
        oldValue, nextInstructions @ [makeCopy src oldValue; increment]
    | C.Unary (operator, exp) ->
        let src, nextInstructions = emitInstruction exp instructions
        let dst = Var <| getTemporaryName ()
        let newInstruction = Unary {| op = convertUnary operator; src = src; dst = dst |}
        dst, nextInstructions @ [newInstruction]
    | C.Binary(And, expLeft, expRight) ->
        let falseLabel = getFalseLabel ()
        let endLabel = getEndLabel ()
        let resultDst = Var <| getTemporaryName ()
        let srcLeft, nextInstructions = emitInstruction expLeft instructions
        let nextInstructions = nextInstructions @ [makeJumpZero srcLeft falseLabel]
        let srcRight, nextInstructions = emitInstruction expRight nextInstructions
        let nextInstructions =
            nextInstructions @ [makeJumpZero srcRight falseLabel; makeCopy (Constant 1) resultDst; Jump endLabel
                                Label falseLabel; makeCopy (Constant 0) resultDst; Label endLabel]
        resultDst, nextInstructions
    | C.Binary(Or, expLeft, expRight) ->
        let trueLabel = getFalseLabel ()
        let endLabel = getEndLabel ()
        let resultDst = Var <| getTemporaryName ()
        let srcLeft, nextInstructions = emitInstruction expLeft instructions
        let nextInstructions = nextInstructions @ [makeJumpNotZero srcLeft trueLabel]
        let srcRight, nextInstructions = emitInstruction expRight nextInstructions
        let nextInstructions =
            nextInstructions @ [makeJumpNotZero srcRight trueLabel; makeCopy (Constant 0) resultDst; Jump endLabel
                                Label trueLabel; makeCopy (Constant 1) resultDst; Label endLabel]
        resultDst, nextInstructions
    | C.Binary(operator, expLeft, expRight) ->
        let srcLeft, nextInstructions = emitInstruction expLeft instructions
        let srcRight, nextInstructions = emitInstruction expRight nextInstructions
        let dst = Var <| getTemporaryName ()
        let newInstruction = Binary {| op = convertBinary operator; srcLeft = srcLeft; srcRight = srcRight; dst = dst |}
        dst, nextInstructions @ [newInstruction]
    | Assignment(C.Var ident, right) ->
        let result, nextInstructions = emitInstruction right instructions
        Var ident, nextInstructions @ [makeCopy result (Var ident)]
    | Assignment(invalid, _) -> failwith $"invalid lvalue {invalid} for assignment"

let fromStatement statement =
    match statement with
    | C.Return expr ->
        let dst, instructions = emitInstruction expr []
        instructions @ [Return dst]
    | Expression expr ->
        let _, instructions = emitInstruction expr []
        instructions
    | Null -> []

let fromDeclaration (ident, exprO) =
    match exprO with
    | None -> []
    | Some expr ->
        let dst, instructions = emitInstruction expr []
        instructions @ [makeCopy dst (Var ident)]

let fromBlockItem blockItem =
    match blockItem with
    | Declaration declaration -> fromDeclaration declaration
    | Statement statement -> fromStatement statement

let fromFunction (C.Function (ident, body))=
    let instructions = (List.collect fromBlockItem body) @ [Return (Constant 0)]
    Function {| name = ident; instructions = instructions |}
    
let fromProgram program =
    match program with
    | C.Program func -> Program <| fromFunction func