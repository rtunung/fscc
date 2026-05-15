module fscc.Assembly

open fscc.Tacky

type Identifier = string

type Reg =
    | AX
    | DX
    | R10
    | R11
    
type UnaryOperator =
    | Neg
    | Not
    
type BinaryOperator =
    | Add
    | Minus
    | Mult

type Operand =
    | Imm of int
    | Reg of Reg
    | Pseudo of Identifier
    | Stack of int

type Instruction =
    | Mov of {|src: Operand; dst: Operand|}
    | Unary of UnaryOperator * Operand
    | Binary of BinaryOperator * Operand * Operand
    | Idiv of Operand
    | Cdq
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
    | Complement -> Not
    | Negate -> Neg

let fromBinaryOperator op =
    match op with
    | Tacky.Minus -> Minus
    | Plus -> Add
    | Multiply -> Mult
    | Remainder
    | Divide -> failwith $"Cannot convert {op} to simple Assembly binary operator"

let fromValue op =
    match op with
    | Constant value -> Imm value
    | Var identifier -> Pseudo identifier
    
let fromInstructions instruction =
    match instruction with
    | Return value ->
        let src = fromValue value
        let mov = Mov {| src = src; dst = Reg AX |}
        [mov; Ret]
    | Tacky.Unary unary ->
        let dst = fromValue unary.dst
        let mov = Mov {| src = fromValue unary.src; dst = dst |}
        [mov; Unary (fromUnaryOperator unary.op, dst)]
    | Tacky.Binary binary when binary.op = Divide ->
        let mov1 = Mov {| src = fromValue binary.srcLeft; dst = Reg AX |}
        let mov2 = Mov {| src = Reg AX; dst = fromValue binary.dst |}
        [mov1; Cdq; Idiv <| fromValue binary.srcRight; mov2]
    | Tacky.Binary binary when binary.op = Remainder ->
        let mov1 = Mov {| src = fromValue binary.srcLeft; dst = Reg AX |}
        let mov2 = Mov {| src = Reg DX; dst = fromValue binary.dst |}
        [mov1; Cdq; Idiv <| fromValue binary.srcRight; mov2]
    | Tacky.Binary binary -> // If we get an error about non-convertible binary operations, then we need to add another case here
        let dst = fromValue binary.dst
        let mov = Mov {| src = fromValue binary.srcLeft; dst = dst |}
        [mov; Binary (fromBinaryOperator binary.op, fromValue binary.srcRight, dst)]

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

let updatePseudo state currentInstr =
    match currentInstr with
    | Unary(unaryOperator, operand) ->
        let updatedOperand, state = replacePseudoOperand state operand
        Unary (unaryOperator, updatedOperand), state
    | Mov mov ->
        let updatedSrc, state = replacePseudoOperand state mov.src
        let updatedDst, state = replacePseudoOperand state mov.dst
        Mov {| src = updatedSrc; dst = updatedDst |}, state
    | Ret -> Ret, state
    | AllocateStack i -> AllocateStack i, state
    | Binary(operator, operand1, operand2) ->
        let updatedOp1, state = replacePseudoOperand state operand1
        let updatedOp2, state = replacePseudoOperand state operand2
        Binary (operator, updatedOp1, updatedOp2), state
    | Idiv operand ->
        let updatedOperand, state = replacePseudoOperand state operand
        Idiv updatedOperand, state
    | Cdq -> Cdq, state
    
let updateInvalidInstructions currentInstr =
    match currentInstr with
    | Mov mov ->
        match mov.src, mov.dst with
        | Stack _, Stack _ ->
            [makeMov mov.src (Reg R10);
            makeMov (Reg R10) mov.dst]
        | _ -> [currentInstr]
    | Idiv operand ->
        match operand with
        | Stack _ -> [makeMov operand (Reg R10); Idiv (Reg R10)]
        | Imm _ -> [makeMov operand (Reg R10); Idiv (Reg R10) ]
        | _ -> [currentInstr]
    | Binary (Mult, left, right) ->
        match right with
        | Stack _ ->
            [makeMov right (Reg R11);
             Binary (Mult, left, Reg R11)
             makeMov (Reg R11) right]
        | _ -> [currentInstr]
    | Binary (operation, left, right) ->
        match left, right with
        | Stack _, Stack _ ->
            [makeMov left (Reg R10)
             Binary (operation, Reg R10, right)]
        | _ -> [currentInstr]
    | Unary _
    | Cdq
    | AllocateStack _
    | Ret -> [currentInstr]


let updateRegisters instructions =
    
    // First replace all Pseudo Registers with stack addresses
    let updatedInstructions, (_, stackSize) =
        instructions
        |> List.mapFold updatePseudo (Map.empty, 0)
        
    // Instructions that have two stack operands are invalid and need to be replaced with valid instructions
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
    | DX -> "%edx"
    | R11 -> "%r11d"

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

let binaryOperatorAssembly op =
    match op with
    | Add -> "addl"
    | Minus -> "subl"
    | Mult -> "imull"

let emitInstruction assembly instruction =
    let nextAssembly =
        match instruction with
        | Ret -> functionEpilogue + "\tret\n"
        | Mov mov -> 
            let src = getOperandAssembly mov.src
            let dst = getOperandAssembly mov.dst
            $"\tmovl {src}, {dst}\n"
        | Unary(unaryOperator, operand) ->
            let instruction = unaryOperatorAssembly unaryOperator
            let operand = getOperandAssembly operand
            $"\t{instruction} {operand}\n"
        | AllocateStack offset -> $"\tsubq ${offset}, {rsp}\n"
        | Binary(operator, left, right) ->
            let instruction = binaryOperatorAssembly operator
            let left = getOperandAssembly left
            let right = getOperandAssembly right
            $"\t{instruction} {left}, {right}\n"
        | Idiv operand ->
            let operand = getOperandAssembly operand
            $"\tidivl {operand}\n"
        | Cdq -> "\tcdq\n"
    
    assembly + nextAssembly

let emitFunction assembly (Function func) =
    let name = func.name
    let newAssembly = assembly + $"\t.globl {name}\n{name}:\n" + functionPrologue
    func.instructions
    |> List.fold emitInstruction newAssembly

let emitProgram program =
    match program with
    | Program f -> emitFunction "" f
    |> fun str -> str + ".section .note.GNU-stack,\"\",@progbits\n"