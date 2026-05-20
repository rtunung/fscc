module fscc.Assembly

open fscc.Tacky

type Identifier = string

type Reg =
    | AX
    | CX
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
    | And
    | Or
    | Xor
    | ShiftRight
    | ShiftLeft

type ConditionalCode =
    | E
    | NE
    | G
    | GE
    | L
    | LE

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
    | Cmp of Operand * Operand
    | Jmp of Identifier
    | JmpCC of ConditionalCode * Identifier
    | SetCC of ConditionalCode * Operand
    | Label of Identifier

type FunctionDefinition =
    Function of {|name : Identifier; instructions : Instruction list|}

type Program = Program of FunctionDefinition

// Helper functions

let isRelationalOperator op =
    match op with
    | GreaterThan
    | LessThan
    | GreaterOrEqual
    | LessOrEqual
    | NotEqual
    | Equal -> true
    | _ -> false
    
let getCCFromOperator op =
    match op with
    | GreaterThan -> G
    | LessThan -> L
    | GreaterOrEqual -> GE
    | LessOrEqual -> LE
    | Equal -> E
    | NotEqual -> NE
    | _ -> failwith "Cannot get Conditional Code from non-relational operator"

let makeMov src dst =
    Mov {| src = src; dst = dst |}

// Generating Assembly from Tacky

let fromUnaryOperator op =
    match op with
    | Complement -> Not
    | Negate -> Neg
    | Tacky.Not -> failwith "Tacky Not cannot be converted into an assembly operator directly"

let fromBinaryOperator op =
    match op with
    | Tacky.Minus -> Minus
    | Plus -> Add
    | Multiply -> Mult
    | Remainder
    | Divide -> failwith $"Cannot convert {op} to simple Assembly binary operator"
    | BitwiseOr -> Or
    | BitwiseAnd -> And
    | BitwiseXor -> Xor
    | Tacky.ShiftLeft -> ShiftLeft
    | Tacky.ShiftRight -> ShiftRight
    
    | LessThan
    | GreaterThan
    | LessOrEqual
    | GreaterOrEqual
    | Equal 
    | NotEqual -> failwith $"Tacky relational operator '{op}' cannot be converted to Assembly binary operators directly"

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
    | Tacky.Unary unary when unary.op = Tacky.Not ->
        let dst = fromValue unary.dst
        let src = fromValue unary.src
        [Cmp (Imm 0, src); makeMov (Imm 0) dst; SetCC (E, dst)]
    | Tacky.Unary unary ->
        let dst = fromValue unary.dst
        let mov = Mov {| src = fromValue unary.src; dst = dst |}
        [mov; Unary (fromUnaryOperator unary.op, dst)]
    | Tacky.Binary binary when isRelationalOperator binary.op ->
        let cc = getCCFromOperator binary.op
        let dst = fromValue binary.dst
        [Cmp (fromValue binary.srcRight, fromValue binary.srcLeft); makeMov (Imm 0) dst; SetCC (cc, dst)]
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
    | Copy copy -> [ makeMov (fromValue copy.src) (fromValue copy.dst) ]
    | Jump label -> [ Jmp label]
    | JumpIfZero jump ->
        [Cmp (Imm 0, fromValue jump.condition); JmpCC (E, jump.target)]
    | JumpIfNotZero jump ->
        [Cmp (Imm 0, fromValue jump.condition); JmpCC (NE, jump.target)]
    | Tacky.Label name-> [Label name]

let fromFunction (Tacky.Function func) =
    let body = List.collect fromInstructions func.instructions
    Function {| name = func.name; instructions = body |}
    
let fromProgram program =
    match program with
    | Tacky.Program func -> Program <| fromFunction func
    
    
// Second compiler pass: converting pseudo addresses to stack addresses

let replacePseudoOperand state operand =
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
    | Binary(operator, operand1, operand2) ->
        let updatedOp1, state = replacePseudoOperand state operand1
        let updatedOp2, state = replacePseudoOperand state operand2
        Binary (operator, updatedOp1, updatedOp2), state
    | Idiv operand ->
        let updatedOperand, state = replacePseudoOperand state operand
        Idiv updatedOperand, state
    | Cdq -> Cdq, state
    | Cmp(src, dst) ->
        let updatedSrc, state = replacePseudoOperand state src
        let updatedDst, state = replacePseudoOperand state dst
        Cmp (updatedSrc, updatedDst), state
    | SetCC(cc, operand) ->
        let updatedOperand, state = replacePseudoOperand state operand
        SetCC (cc, updatedOperand), state
        
    | Jmp _
    | JmpCC _
    | Label _
    | Ret
    | AllocateStack _ -> currentInstr, state

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
        | Stack _
        | Imm _ -> [makeMov operand (Reg R10); Idiv (Reg R10) ]
        | _ -> [currentInstr]
    | Binary (Mult, src, dst) -> // imul cant use a memory address as destination, so we are using R11
        match dst with
        | Stack _ ->
            [makeMov dst (Reg R11);
             Binary (Mult, src, Reg R11)
             makeMov (Reg R11) dst]
        | _ -> [currentInstr]
    | Binary (shift, src, dst) when shift = ShiftLeft || shift = ShiftRight -> // Shift operation needs CX as source
        match src with
        | Reg CX -> [currentInstr]
        | Imm _ -> [currentInstr]
        | _ ->
            [makeMov src (Reg CX);
             Binary (shift, Reg CX, dst)]
    | Binary (operation, src, dst) ->
        match src, dst with
        | Stack _, Stack _ ->
            [makeMov src (Reg R10)
             Binary (operation, Reg R10, dst)]
        | _ -> [currentInstr]
    | Cmp(src, dst) ->
        match src, dst with
        | Stack _, Stack _ -> [makeMov src (Reg R10); Cmp (Reg R10, dst)] // Can't operate on two memory addresses
        | _, Imm x -> [makeMov (Imm x) (Reg R11); Cmp (src, Reg R11)] // The second operand cannot be a constant
        | _, _ -> [currentInstr]
    | Jmp _
    | JmpCC _
    | SetCC _
    | Label _
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
    | CX -> "%ecx"

let getRegisterAssembly1Byte reg =
    match reg with
    | AX -> "%al"
    | DX -> "%dl"
    | CX -> "%cl"
    | R10 -> "%r10b"
    | R11 -> "%r11b"

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
    | And -> "andl"
    | Or -> "orl"
    | Xor -> "xorl"
    | ShiftRight -> "sar" // Currently using arithmetic shift; In the future we might need logical shift
    | ShiftLeft -> "shl"

let getCCSuffix cc =
    match cc with
    | E -> "e"
    | NE -> "ne"
    | G -> "g"
    | GE -> "ge"
    | L -> "l"
    | LE -> "le"

let getLabelAssembly (label:Identifier) = $".L{label}"

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
        | Binary(shift, Reg CX, right) when shift = ShiftLeft || shift = ShiftRight ->
            let instruction = binaryOperatorAssembly shift
            let left = getRegisterAssembly1Byte CX
            let right = getOperandAssembly right
            $"\t{instruction} {left}, {right}\n"
        | Binary(operator, left, right) ->
            let instruction = binaryOperatorAssembly operator
            let left = getOperandAssembly left
            let right = getOperandAssembly right
            $"\t{instruction} {left}, {right}\n"
        | Idiv operand ->
            let operand = getOperandAssembly operand
            $"\tidivl {operand}\n"
        | Cdq -> "\tcdq\n"
        | Cmp(left, right) ->
            let left = getOperandAssembly left
            let right = getOperandAssembly right
            $"\tcmpl {left}, {right}\n"
        | Jmp label ->
            let labelName = getLabelAssembly label
            $"\tjmp {labelName}\n"
        | Label label ->
            let labelName = getLabelAssembly label
            $"{labelName}:\n"
        | JmpCC(cc, target) ->
            let suffix = getLabelAssembly target
            let ccStr = getCCSuffix cc
            $"\tj{ccStr} {suffix}\n"
        | SetCC(cc, operand) ->
            let suffix = getCCSuffix cc
            let operand = getOperandAssembly operand
            $"\tset{suffix} {operand}\n"

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