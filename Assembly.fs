module fscc.Assembly

open System.Runtime.InteropServices.ComTypes
open fscc.SemanticAnalysis
open fscc.Tacky

type Identifier = string

type Reg =
    | AX
    | CX
    | DX
    | DI
    | SI
    | R8
    | R9
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
    | Data of Identifier

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
    | DeallocateStack of int
    | Push of Operand
    | Call of Identifier

type TopLevel =
    | Function of name: Identifier * globl: bool * instructions: Instruction list
    | StaticVariable of name: Identifier * globl: bool * init: int

type Program = Program of TopLevel list

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

let functionCallRegisters = [DI; SI; DX; CX; R8; R9]

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
    | FunctionCall(name, arguments, dst) ->
        
        let registerArgs, stackArgs =
            if (List.length arguments) >= 6
            then List.splitAt 6 arguments
            else arguments, []
            
        let stackArgsLength = List.length stackArgs
        let stackPadding =
            if stackArgsLength % 2 = 0
            then 0
            else 8
        
        let stackPaddingInstruction =
            if stackPadding <> 0 then [AllocateStack stackPadding]
            else []
            
        let movRegisterArgs =
            registerArgs
            |> List.zip (List.truncate (List.length registerArgs) functionCallRegisters)
            |> List.map (fun (reg, value) -> makeMov (fromValue value) (Reg reg))
        
        let makeMovStackArgs arg =
            let assemblyArg = fromValue arg
            match assemblyArg with
            | Reg _
            | Imm _ -> [Push assemblyArg]
            | Pseudo _
            | Data _
            | Stack _ -> [makeMov assemblyArg (Reg AX); Push (Reg AX)]

        let movStackArgs =
            stackArgs
            |> List.rev
            |> List.collect makeMovStackArgs
            
        let funcCall = [Call name]
        
        let bytesToRemove = 8 * stackArgsLength + stackPadding
        let deallocateStackInstruction =
            if bytesToRemove <> 0
            then [DeallocateStack bytesToRemove]
            else []
            
        let retrieveFromAx = [makeMov (Reg AX) (fromValue dst)]
        
        List.concat [stackPaddingInstruction; movRegisterArgs; movStackArgs
                     funcCall; deallocateStackInstruction; retrieveFromAx]
        
        

let passFunctionParameters parameters =
    let rec passWithState (availableRegisters, stackArgs) acc parameters =
        match parameters with
        | [] -> acc
        | para :: rest ->
            match availableRegisters with
            | reg :: restReg ->
                let instructions = acc @ [makeMov (Reg reg) (Pseudo para)]
                passWithState (restReg, stackArgs) instructions rest
            | [] ->
                let instructions = acc @ [makeMov (Stack stackArgs) (Pseudo para)]
                let stackArgs = stackArgs + 8
                passWithState ([], stackArgs) instructions rest
                
    passWithState (functionCallRegisters, 16) [] parameters

let fromTopLevel topLevel=
    match topLevel with
    | Tacky.Function (name, globl, parameters, instructions) ->
        let copyParameters = passFunctionParameters parameters
        let bodyInstructions = List.collect fromInstructions instructions
        Function (name, globl, copyParameters @ bodyInstructions)
    | Tacky.StaticVariable(name, globl, init) ->
        StaticVariable (name, globl, init)

let fromProgram program =
    match program with
    | Tacky.Program func ->
        func
        |> List.map fromTopLevel
        |> Program
    
    
// ---------------------------------- Second Assembly pass -----------------------------------------

// ------------------------------- Converting pseudo registers  ------------------------------------

(*
    This stage updated the Pseudo Registers to usable Stack Addresses.
    The stack size per function is also calculated in this step
*)

let replacePseudoOperand state symbolTable operand =
    let map, counter = state
    match operand with
    | Pseudo name ->
        if Map.containsKey name map then
            let stackOperand = Stack <| Map.find name map
            stackOperand, (map, counter)
        else
            match Map.tryFind name symbolTable with
            | Some foundSymbol when isStaticSymbol foundSymbol ->
                let newOperand = Data name
                newOperand, (map, counter)
            | _ ->
                let updatedCounter = counter - 4
                let pos = updatedCounter
                let updatedMap = Map.add name pos map
                let stackOperand = Stack <| pos
                stackOperand, (updatedMap, updatedCounter)
    | nonPseudo -> nonPseudo, (map, counter)

let updatePseudoInstruction state symbolTable currentInstr =
    let replaceOperand state operand = replacePseudoOperand state symbolTable operand
    match currentInstr with
    | Unary(unaryOperator, operand) ->
        let updatedOperand, state = replaceOperand state operand
        Unary (unaryOperator, updatedOperand), state
    | Mov mov ->
        let updatedSrc, state = replaceOperand state mov.src
        let updatedDst, state = replaceOperand state mov.dst
        Mov {| src = updatedSrc; dst = updatedDst |}, state
    | Binary(operator, operand1, operand2) ->
        let updatedOp1, state = replaceOperand state operand1
        let updatedOp2, state = replaceOperand state operand2
        Binary (operator, updatedOp1, updatedOp2), state
    | Idiv operand ->
        let updatedOperand, state = replaceOperand state operand
        Idiv updatedOperand, state
    | Cdq -> Cdq, state
    | Cmp(src, dst) ->
        let updatedSrc, state = replaceOperand state src
        let updatedDst, state = replaceOperand state dst
        Cmp (updatedSrc, updatedDst), state
    | SetCC(cc, operand) ->
        let updatedOperand, state = replaceOperand state operand
        SetCC (cc, updatedOperand), state
    | Push operand ->
        let updatedOperand, state = replaceOperand state operand
        Push updatedOperand, state
        
    | Jmp _
    | JmpCC _
    | Label _
    | Ret
    | Call _
    | DeallocateStack _
    | AllocateStack _ -> currentInstr, state

let updatePseudoInstructions symbolTable instructions =
    let updateInstruction state instruction = updatePseudoInstruction state symbolTable instruction
    let updatedInstructions, (_, stackSize) =
        instructions
        |> List.mapFold updateInstruction (Map.empty, 0)
    
    updatedInstructions, -stackSize
        

// ------------------------------------ Update Invalid Instructions ------------------------------------

let isMemoryOperand operand =
    match operand with
    | Stack _
    | Data _ -> true
    | _ -> false

let updateInvalidInstruction currentInstr =
    match currentInstr with
    | Mov mov ->
        match mov.src, mov.dst with
        | memA, memB  when isMemoryOperand memA && isMemoryOperand memB ->
            [makeMov mov.src (Reg R10);
            makeMov (Reg R10) mov.dst]
        | _ -> [currentInstr]
    | Idiv operand ->
        match operand with
        | Stack _
        | Data _
        | Imm _ -> [makeMov operand (Reg R10); Idiv (Reg R10) ]
        | _ -> [currentInstr]
    | Binary (Mult, src, dst) -> // imul cant use a memory address as destination, so we are using R11
        match dst with
        | mem when isMemoryOperand mem ->
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
        | memA, memB when isMemoryOperand memA && isMemoryOperand memB ->
            [makeMov src (Reg R10)
             Binary (operation, Reg R10, dst)]
        | _ -> [currentInstr]
    | Cmp(src, dst) ->
        match src, dst with
        | memA, memB when isMemoryOperand memA && isMemoryOperand memB ->
            [makeMov src (Reg R10); Cmp (Reg R10, dst)] // Can't operate on two memory addresses
        | _, Imm x -> [makeMov (Imm x) (Reg R11); Cmp (src, Reg R11)] // The second operand cannot be a constant
        | _, _ -> [currentInstr]
    | Jmp _
    | JmpCC _
    | SetCC _
    | Label _
    | Unary _
    | Cdq
    | AllocateStack _
    | DeallocateStack _
    | Push _
    | Call _

    | Ret -> [currentInstr]

// ------------------------------------------ The actual second Assembly pass -----------------------------------------

let updateTopLevel symbolTable topLevel =
    match topLevel with
    |  Function(name, globl, instructions) ->
        let instructions, stackSize = updatePseudoInstructions symbolTable instructions
        
        let neededToBeMultipleOf16 = (16 - (stackSize % 16)) % 16
        let roundedStackSize = stackSize + neededToBeMultipleOf16
        let updatedInstructions =
            instructions
            |> List.collect updateInvalidInstruction
            |> (@) [AllocateStack roundedStackSize]
            
        Function (name, globl, updatedInstructions)
    | StaticVariable _ -> topLevel

let updateProgram symbolTable (Program functions) =
    functions
    |> List.map (updateTopLevel symbolTable)
    |> Program
    

// ------------------------------------- Emitting Assembly -----------------------------------

let getRegisterAssembly reg =
    match reg with
    | AX -> "%eax"
    | CX -> "%ecx"
    | DX -> "%edx"
    | SI -> "%esi"
    | DI -> "%edi"
    | R8 -> "%r8d"
    | R9 -> "%r9d"
    | R10 -> "%r10d"
    | R11 -> "%r11d"

let getRegisterAssembly8Byte reg =
    match reg with
    | AX -> "%rax"
    | CX -> "%rcx"
    | DX -> "%rdx"
    | SI -> "%rsi"
    | DI -> "%rdi"
    | R8 -> "%r8"
    | R9 -> "%r9"
    | R10 -> "%r10"
    | R11 -> "%r11"

let getRegisterAssembly1Byte reg =
    match reg with
    | AX -> "%al"
    | CX -> "%cl"
    | DX -> "%dl"
    | SI -> "%sil"
    | DI -> "%dil"
    | R8 -> "%8b"
    | R9 -> "%9b"
    | R10 -> "%r10b"
    | R11 -> "%r11b"

let rbp = "%rbp"
let rsp = "%rsp"
let rip = "%rip"
let functionPrologue = "\tpushq %rbp\n\tmovq %rsp, %rbp\n"
let functionEpilogue = "\tmovq %rbp, %rsp\n\tpopq %rbp\n"

let alignmentDirective = ".align 4"

let getOperandAssembly operand =
    match operand with
    | Imm value -> $"${value}"
    | Reg reg -> getRegisterAssembly reg
    | Stack offset -> $"{offset}({rbp})"
    | Data name -> $"{name}({rip})"
    | Pseudo name -> failwith $"Found pseudo register {name} during assembly generation. This is a compiler bug!"

let getOperandAssembly8Byte operand =
    match operand with
    | Reg reg -> getRegisterAssembly8Byte reg
    | _ -> getOperandAssembly operand

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

let emitInstruction instruction =
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
        | DeallocateStack offset -> $"\taddq ${offset}, {rsp}\n"
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
        | Push operand ->
            let operand = getOperandAssembly8Byte operand
            $"\tpushq {operand}\n"
        | Call label -> $"\tcall {label}\n"
    
    nextAssembly

let emitTopLevel topLevel =
    let globlDirective globl name = if globl then $"\t.globl {name}\n" else ""
    match topLevel with
    | Function(name, globl, instructions) ->
        let functionHeader = $"{globlDirective globl name}\t.text\n{name}:\n" + functionPrologue
        instructions
        |> List.map emitInstruction
        |> String.concat ""
        |> fun str -> functionHeader + str + "\n"
    | StaticVariable(name, globl, 0) ->
        $"{globlDirective globl name}\n\t.bss\n\t{alignmentDirective}\n{name}:\n\t.zero 4\n\n"
    | StaticVariable(name, globl, init) ->
        $"{globlDirective globl name}\n\t.data\n\t{alignmentDirective}\n{name}:\n\t.long {init}\n\n"

let emitProgram (Program functions) =
    functions
    |> List.map emitTopLevel
    |> fun x -> x @ [".section .note.GNU-stack,\"\",@progbits\n"]
    |> String.concat ""