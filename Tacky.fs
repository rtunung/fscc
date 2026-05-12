module fscc.Tacky

open fscc.CAst

type Identifier = string

type UnaryOperator =
    | Complement
    | Negate
    
type Value =
    | Constant of int
    | Var of Identifier
    
type Instruction =
    | Return of Value
    | Unary of {| op : UnaryOperator; src : Value; dst : Value |}
    
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

let rec emitInstruction expression instructions =
    match expression with
    | CAst.Constant value -> Constant value, instructions
    | CAst.Unary (operator, exp) ->
        let src, nextInstructions = emitInstruction exp instructions
        let dst = Var <| getTemporaryName ()
        let newInstruction = Unary {| op = convertUnary operator; src = src; dst = dst |}
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