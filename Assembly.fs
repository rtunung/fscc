module fscc.Assembly

type Identifier = string

type Reg =
    | AX
    | R10
    
type UnaryOperator =
    | Neg
    | Not

type Operand =
    | Imm of int
    | Reg of Reg
    | Pseudo of Identifier
    | Stack of int

type Instruction =
    | Mov of {|src: Operand; dst: Operand|}
    | Unary of UnaryOperator * Operand
    | AllocateStack of int
    | Ret

type FunctionDefinition =
    Function of {|name : Identifier; instructions : Instruction list|}

type Program = Program of FunctionDefinition

// Generating Assembly from Tacky

let makeMov src dst =
    Mov {| src = src; dst = dst |}

let fromUnaryOperator op =
    match op with
    | Tacky.Complement -> Not
    | Tacky.Negate -> Neg
    
let fromValue op =
    match op with
    | Tacky.Constant value -> Imm value
    | Tacky.Var identifier -> Pseudo identifier
    
let fromInstructions instruction =
    match instruction with
    | Tacky.Return value ->
        let src = fromValue value
        let mov = Mov {| src = src; dst = Reg AX |}
        [mov; Ret]
    | Tacky.Unary unary ->
        let dst = fromValue unary.dst
        let mov = Mov {| src = fromValue unary.src; dst = dst |}
        [mov; Unary (fromUnaryOperator unary.op, dst)]
        
let fromFunction (Tacky.Function func) =
    let body = List.collect fromInstructions func.instructions
    Function {| name = func.name; instructions = body |}
    
let fromProgram program =
    match program with
    | Tacky.Program func -> Program <| fromFunction func
    
    
    
// Second compiler pass: converting pseudo addresses to stack addresses

let replacePseudoOperand state operand=
    let map, counter = state
    match operand with
    | Pseudo name ->
        if Map.containsKey name map then
            let stackOperand = Stack <| Map.find name map
            stackOperand, (map, counter)
        else
            let updatedCounter = counter - 4
            let pos = updatedCounter
            let updatedMap = Map.add name pos map
            let stackOperand = Stack <| pos
            stackOperand, (updatedMap, updatedCounter)
    | nonPseudo -> nonPseudo, (map, counter)

let updateRegisters instructions =
    
    // First replace all Pseudo Registers with stack addresses
    let updatePseudo (map, counter) currentInstr =
        match currentInstr with
        | Unary(unaryOperator, operand) ->
            let updatedOperand, (updatedMap, updatedCounter) = replacePseudoOperand (map, counter) operand
            Unary (unaryOperator, updatedOperand), (updatedMap, updatedCounter)
        | Mov mov ->
            let updatedSrc, (updatedMap, updatedCounter) = replacePseudoOperand (map, counter) mov.src
            let updatedDst, (updatedMap, updatedCounter) = replacePseudoOperand (updatedMap, updatedCounter) mov.dst
            Mov {| src = updatedSrc; dst = updatedDst |}, (updatedMap, updatedCounter)
        | other -> other, (map, counter)
        
    let updatedInstructions, (_, stackSize) =
        instructions
        |> List.mapFold updatePseudo (Map.empty, 0)
        
    // Instructions, that have two stack operands are invalid and need to be replaced with valid instructions
    let updateInvalidInstructions currentInstr =
        match currentInstr with
        | Mov mov ->
            match mov.src, mov.dst with
            | Stack _, Stack _ ->
                [makeMov mov.src (Reg R10);
                makeMov (Reg R10) mov.dst]
            | _ -> [Mov mov]
        | other -> [other]
    
    updatedInstructions
    |> List.collect updateInvalidInstructions
    |> (@) [AllocateStack stackSize]

let updateAllInstructions program =
    let (Program (Function func)) = program
    Program <| Function {| func with instructions = updateRegisters func.instructions |}
    

// Emitting assembly code from Assembly AST

let getRegisterAssembly reg =
    match reg with
    | AX -> "%eax"
    | R10 -> "%r10d"
    
let rbp = "%rbp"
let rsp = "%rsp"
let functionPrologue = "\tpushq %rbp\n\tmovq %rsp, %rbp\n"
let functionEpilogue = "\tmovq %rbp, %rsp\n\tpopq %rbp\n"

let getOperandAssembly operand =
    match operand with
    | Imm value -> $"${value}"
    | Reg reg -> getRegisterAssembly reg
    | Stack offset -> $"{offset}({rbp})"
    | Pseudo name -> failwith $"Found pseudo register {name} during assembly generation. This is a compiler bug!"

let unaryOperatorAssembly op =
    match op with
    | Neg -> "negl"
    | Not -> "notl"

let emitInstruction assembly instruction =
    match instruction with
    | Ret -> assembly + functionEpilogue + "\tret\n"
    | Mov mov -> 
        let src = getOperandAssembly mov.src
        let dst = getOperandAssembly mov.dst
        assembly + $"\tmovl {src}, {dst}\n"
    | Unary(unaryOperator, operand) ->
        let operator = unaryOperatorAssembly unaryOperator
        let operand = getOperandAssembly operand
        assembly + $"\t{operator} {operand}\n"
    | AllocateStack offset -> assembly + $"\tsubq ${offset}, {rsp}\n"

let emitFunction assembly (Function func) =
    let name = func.name
    let newAssembly = assembly + $"\t.globl {name}\n{name}:\n" + functionPrologue
    func.instructions
    |> List.fold emitInstruction newAssembly

let emitProgram program =
    match program with
    | Program f -> emitFunction "" f
    |> fun str -> str + ".section .note.GNU-stack,\"\",@progbits\n"