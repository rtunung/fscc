module fscc.Tacky

open fscc.C

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

// Global mutable state, very evil
let mutable tempVariableCounter = 0
let getTemporaryName () =
    let name = $"temp.{tempVariableCounter}"
    tempVariableCounter <- tempVariableCounter + 1
    Identifier name
    
let mutable falseLabelCounter = 0
let getFalseLabel () =
    let label = $"false.{falseLabelCounter}"
    falseLabelCounter <- falseLabelCounter + 1
    Identifier label
    
let mutable endLabelCounter = 0
let getEndLabel () =
    let label = $"end.{endLabelCounter}"
    endLabelCounter <- endLabelCounter + 1
    Identifier label
    
let convertUnary unary =
    match unary with
    | C.Complement -> Complement
    | C.Negate -> Negate
    | C.Not -> Not

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
    | C.Unary (operator, exp) ->
        let src, nextInstructions = emitInstruction exp instructions
        let dst = Var <| getTemporaryName ()
        let newInstruction = Unary {| op = convertUnary operator; src = src; dst = dst |}
        dst, nextInstructions @ [newInstruction]
    | C.Binary(C.And, expLeft, expRight) ->
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
    | C.Binary(C.Or, expLeft, expRight) ->
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

let fromStatement statement =
    match statement with
    | C.Return expr ->
        let dst, instructions = emitInstruction expr []
        instructions @ [Return dst]
        
let fromFunction (C.Function func) =
    let instructions = fromStatement func.instructions
    Function {| name = func.name; instructions = instructions |}
    
let fromProgram program =
    match program with
    | C.Program func -> Program <| fromFunction func