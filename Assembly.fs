module fscc.Assembly

type Identifier = Identifier of string

type Operand =
    | Imm of int
    | Register

type Instruction =
    | Mov of {|src: Operand; dst: Operand|}
    | Ret

type FunctionDefinition =
    Function of {|name : Identifier; instructions : Instruction list|}

type Program = Program of FunctionDefinition

let identifierToIdentifier ident =
    match ident with
    | Parser.Identifier value -> Identifier value

let expressionToOperand exp =
    match exp with
    | Parser.Constant value -> Imm value

let statementToInstructions statement =
    match statement with
    | Parser.Return value ->
        let operand = expressionToOperand value
        [Mov {| src = operand; dst = Register |}; Ret]

let functionToFunction func =
    match func with
    | Parser.Function f ->
        let instructions = statementToInstructions f.body
        Function {|name = identifierToIdentifier f.name; instructions = instructions|}

let toAssemblyProgram program =
    match program with
    | Parser.Program f -> Program <| functionToFunction f


// Emitting assembly code from Assembly AST

let nameOfIdentifier identifier =
    match identifier with
    | Identifier value -> value

let getOperandAssembly operand =
    match operand with
    | Register -> "%eax"
    | Imm value -> $"${value}"

let emitInstruction assembly instruction =
    match instruction with
    | Ret -> assembly + "\tret\n"
    | Mov mov -> 
        let src = getOperandAssembly mov.src
        let dst = getOperandAssembly mov.dst
        assembly + $"\tmovl {src}, {dst}\n"

let emitFunction assembly (Function func) =
    let (Identifier name) = func.name
    let newAssembly = assembly + $"\t.globl {name}\n{name}:\n"
    func.instructions
    |> List.fold emitInstruction newAssembly

let emitProgram program =
    match program with
    | Program f -> emitFunction "" f
    |> fun str -> str + ".section .note.GNU-stack,\"\",@progbits\n"