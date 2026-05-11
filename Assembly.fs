module fscc.Assembly

type Identifier = Identifier of string

type Operand =
    | Imm of int
    | Register

type Instruction =
    | Mov of {|Src : Operand; Dst : Operand|}
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
        [Mov {|Src = operand; Dst = Register |}; Ret]

let functionToFunction func =
    match func with
    | Parser.Function f ->
        let instructions = statementToInstructions f.body
        Function {|name = identifierToIdentifier f.name; instructions = instructions|}

let programToAssemblyProgram program =
    match program with
    | Parser.Program f -> Program <| functionToFunction f
