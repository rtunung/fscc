module fscc.Tacky

open fscc.CAst

type Identifier = string

type UnaryOperator =
    | Complement
    | Negate
    
type BinaryOperator =
    | Minus
    | Plus
    | Divide
    | Multiply
    | Remainder
    | Or
    | And
    | Xor
    | ShiftLeft
    | ShiftRight
    
type Value =
    | Constant of int
    | Var of Identifier
    
type Instruction =
    | Return of Value
    | Unary of {| op : UnaryOperator; src : Value; dst : Value |}
    | Binary of {| op: BinaryOperator; srcLeft : Value; srcRight : Value; dst : Value |}
    
type FunctionDefinition =
    Function of {| name : Identifier; instructions: Instruction list |}
    
type Program =
    Program of FunctionDefinition
    
// Global mutable state, very evil
let mutable tempVariableCounter = 0
let getTemporaryName () =
    let name = $"temp.{tempVariableCounter}"
    tempVariableCounter <- tempVariableCounter + 1
    Identifier name
    
let convertUnary unary =
    match unary with
    | CAst.Complement -> Complement
    | CAst.Negate -> Negate
    
let converBinary binary =
    match binary with
    | CAst.Plus -> Plus
    | CAst.Minus -> Minus
    | CAst.Multiply -> Multiply
    | CAst.Divide -> Divide
    | CAst.Remainder -> Remainder
    | CAst.Or -> Or
    | CAst.And -> And
    | CAst.Xor -> Xor
    | CAst.ShiftLeft -> ShiftLeft
    | CAst.ShiftRight -> ShiftRight

let rec emitInstruction expression instructions =
    match expression with
    | CAst.Constant value -> Constant value, instructions
    | CAst.Unary (operator, exp) ->
        let src, nextInstructions = emitInstruction exp instructions
        let dst = Var <| getTemporaryName ()
        let newInstruction = Unary {| op = convertUnary operator; src = src; dst = dst |}
        dst, nextInstructions @ [newInstruction]
    | CAst.Binary(operator, expLeft, expRight) ->
        let srcLeft, nextInstructions = emitInstruction expLeft instructions
        let srcRight, nextInstructions = emitInstruction expRight nextInstructions
        let dst = Var <| getTemporaryName ()
        let newInstruction = Binary {| op = converBinary operator; srcLeft = srcLeft; srcRight = srcRight; dst = dst |}
        dst, nextInstructions @ [newInstruction]

let fromStatement statement =
    match statement with
    | CAst.Return expr ->
        let dst, instructions = emitInstruction expr []
        instructions @ [Return dst]
        
let fromFunction (CAst.Function func) =
    let instructions = fromStatement func.instructions
    Function {| name = func.name; instructions = instructions |}
    
let fromProgram program =
    match program with
    | CAst.Program func -> Program <| fromFunction func