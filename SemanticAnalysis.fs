module fscc.SemanticAnalysis

open C
open Misc
open FsToolkit.ErrorHandling

// -------------------------------------- Helper Functions -----------------------------------------------------------

let private isIncrementDecrement op =
    match op with
    | PostfixDecrement
    | PrefixDecrement
    | PostfixIncrement
    | PrefixIncrement -> true
    | _ -> false

// ------------------------------------- Resolve Identifiers --------------------------------------------------

(*
    The identifiers names need to be mapped to globally unique names.
    However, identifiers with external linkage need to keep their original name, otherwise linking will fail.
    To achieve this, we need to track a state as we resolve the new identifier names.
    The state has the following members:
    - identifierMap: A map from in C defined identifiers to globally unique identifiers
                     This table is also used to store linkage information
    - scopeSet: A set that contains all variable names that are declared in the current scope (Does not include parent or child blocks)
        -> Detect multiple declarations in the same block.
        -> Allows for shadowing of variable identifiers once you go into a child block
   - linkageSet: A set that tracks which identifiers are externally linked
*)


let rec resolveExpression expr (identifierMap:Map<Identifier, Identifier>) =
    match expr with
    | Assignment (Var left, right) -> result {
        let! left = resolveExpression (Var left) identifierMap
        let! right = resolveExpression right identifierMap
        return Assignment (left, right)
        }
    | Assignment (invalid, _) -> Error <| Message $"Invalid lvalue {invalid}"
    | Var name when Map.containsKey name identifierMap ->
        let uniqueName = Map.find name identifierMap
        Ok (Var uniqueName)
    | Var undeclared -> Error <| Message $"Variable {undeclared} is undeclared"
    | Constant _ -> Ok expr
    | Unary (inc, Var a) when isIncrementDecrement inc -> result {
        let! expr = resolveExpression (Var a) identifierMap
        return Unary (inc, expr)
        }
    | Unary (inc, invalid) when isIncrementDecrement inc -> Error <| Message $"Invalid lvalue {invalid} for operator {inc}"
    | Unary(operator, expression) -> result {
        let! expression = resolveExpression expression identifierMap
        return Unary(operator, expression)
        }
    | Binary(operator, left, right) -> result {
        let! left = resolveExpression left identifierMap
        let! right = resolveExpression right identifierMap
        return Binary(operator, left, right)
        }
    | Conditional(cond, middle, right) -> result {
        let! cond = resolveExpression cond identifierMap
        let! middle = resolveExpression middle identifierMap
        let! right = resolveExpression right identifierMap
        return Conditional(cond, middle, right)
        }
    | FunctionCall(name, args) ->
        if Map.containsKey name identifierMap then
            let name = Map.find name identifierMap
            let resolvedArgsResult =
                args
                |> Seq.map (fun x -> resolveExpression x identifierMap)
                |> Seq.sequenceResultM
                |> Result.map Array.toList
            match resolvedArgsResult with
            | Error error -> Error error
            | Ok resolvedArgs -> Ok (FunctionCall (name, resolvedArgs))
        else
            Error <| Message $"Function identifier {name} was not declared"

let rec resolveStatement statement (identifierMap, scopeSet, linkageSet) =
    match statement with
    | Null -> Ok (Null, linkageSet)
    | Return expr -> result {
        let! expr = resolveExpression expr identifierMap
        return Return expr, linkageSet
        }
    | Expression expr ->  result {
        let! expr = resolveExpression expr identifierMap
        return Expression expr, linkageSet
        }
    | If (cond, ifBody, elseBody) -> result {
        let! cond = resolveExpression cond identifierMap
        let! ifBody, linkageSet = resolveStatement ifBody (identifierMap, scopeSet, linkageSet)
        match elseBody with
        | None -> return If (cond, ifBody, None), linkageSet
        | Some elseBody ->
            let! elseBody, linkageSet = resolveStatement elseBody (identifierMap, scopeSet, linkageSet)
            return If (cond, ifBody, Some elseBody), linkageSet
            }
    | Label (name, labelStatement) -> result {
        let! labelStatement, linkageSet = resolveStatement labelStatement (identifierMap, scopeSet, linkageSet)
        return Label (name, labelStatement), linkageSet
        }
    | Goto _ -> Ok (statement, linkageSet)
    | Compound block ->  result {
        let! newBlock, linkageSet = resolveBlock block (identifierMap, Set.empty, linkageSet)
        return Compound newBlock, linkageSet
        }
    | DummyBreak -> Ok (statement, linkageSet)
    | DummyContinue -> Ok (statement, linkageSet)
    | DummyWhile(cond, body) -> result {
        let! resolvedCond = resolveExpression cond identifierMap
        let! resolvedBody, linkageSet = resolveStatement body (identifierMap, scopeSet, linkageSet)
        return DummyWhile (resolvedCond, resolvedBody), linkageSet
        }
    | DummyDoWhile(body, cond) -> result {
        let! resolvedBody, linkageSet = resolveStatement body (identifierMap, scopeSet, linkageSet)
        let! resolvedCond = resolveExpression cond identifierMap
        return DummyDoWhile (resolvedBody, resolvedCond), linkageSet
        }
    | DummyFor(init, cond, post, body) -> result {
        let! resolvedInit, (identifierMap, scopeSet, linkageSet) = resolveForInit init (identifierMap, linkageSet)
        let! resolvedCond = resolveOptionalExpression cond identifierMap
        let! resolvedPost = resolveOptionalExpression post identifierMap
        let! resolvedBody, linkageSet = resolveStatement body (identifierMap, scopeSet, linkageSet)
        return DummyFor (resolvedInit, resolvedCond, resolvedPost, resolvedBody), linkageSet
        }
    | DummySwitch (argument, body) -> result {
        let! resolvedArgument = resolveExpression argument identifierMap
        let! resolvedBody, linkageSet = resolveStatement body (identifierMap, scopeSet, linkageSet)
        return DummySwitch (resolvedArgument,  resolvedBody), linkageSet
        }
    | DummyCase (case, body) -> result {
        let! resolvedCase = resolveExpression case identifierMap
        let! resolvedBody, linkageSet = resolveStatement body (identifierMap, scopeSet, linkageSet)
        return DummyCase (resolvedCase, resolvedBody), linkageSet
        }
    | DummyDefault body -> result {
        let! resolvedBody, linkageSet = resolveStatement body (identifierMap, scopeSet, linkageSet)
        return DummyDefault resolvedBody, linkageSet
        }
        
    | LoopBreak _
    | Continue _
    | DoWhile _
    | For _ 
    | While _ -> failwith "Variable resolution needs to be performed before loop labeling"

    | Switch _
    | Case _
    | Default _
    | SwitchBreak _ -> failwith "Variable resolution needs to be performed before switch labeling"


and resolveOptionalExpression expr identifierMap =
    expr
    |> Option.map (fun x ->  resolveExpression x identifierMap)
    |> Option.sequenceResult
    
and resolveForInit init (identifierMap, linkageSet)=
    match init with
    | InitExpression None -> Ok (InitExpression None, (identifierMap, Set.empty, linkageSet))
    | InitExpression (Some expr) -> result {
        let! resolvedExpr = resolveExpression expr identifierMap
        return InitExpression (Some resolvedExpr), (identifierMap, Set.empty, linkageSet)
        }
    | InitDeclaration declaration -> result {
        let! resolvedDecl, state = resolveLocalVariableDeclaration declaration (identifierMap, Set.empty, linkageSet)
        return InitDeclaration resolvedDecl, state
        }

and resolveBlockItem item (identifierMap, scopeSet, linkageSet) =
    match item with
    | Declaration (VariableDecl declaration) -> result {
        let! resolvedDecl, state = resolveLocalVariableDeclaration declaration (identifierMap, scopeSet, linkageSet)
        return Declaration (VariableDecl resolvedDecl), state
        }
    | Declaration (FunctionDecl (Function (_, _, None, _) as func)) -> result {
        let! resolvedFunc, state = resolveFunctionDeclaration func (identifierMap, scopeSet, linkageSet)
        return Declaration (FunctionDecl resolvedFunc), state
        }
    | Declaration (FunctionDecl (Function (name, _, _, _))) -> Error <| Message $"Nested function definition are invalid. Function: {name}" 
    | Statement statement -> result {
        let! statement, linkageSet = resolveStatement statement (identifierMap, scopeSet, linkageSet)
        return Statement statement, (identifierMap, scopeSet, linkageSet)
        }
    
and resolveBlock items (identifierMap, scopeSet, linkageSet) =
    let rec loop items (_,_,linkageSet as state) acc =
        match items with
        | [] -> Ok (acc, linkageSet)
        | item :: rest ->
            let resolvedItem = resolveBlockItem item state
            match resolvedItem with
            | Error error -> Error error
            | Ok (newItem, state) -> loop rest state (acc @ [newItem])
    
    loop items (identifierMap, scopeSet, linkageSet) []
   
   
// Resolve local variable declarations opposed to file scope declarations
and resolveLocalVariableDeclaration (Variable (ident, expr, storageClass)) (identifierMap, scopeSet, linkageSet) =
    
    let resolveVariable () =
        match storageClass with
        | Some Extern ->
            let identifierMap = Map.add ident ident identifierMap
            let scopeSet = Set.add ident scopeSet
            let linkageSet = Set.add ident linkageSet
            Ok (Variable (ident, expr, storageClass), (identifierMap, scopeSet, linkageSet))
        | _ ->
            let uniqueName = Identifier (getTemporaryName ())
            let identifierMap = Map.add ident uniqueName identifierMap
            let blockSet = Set.add ident scopeSet
    
            let expr = Option.map (fun x -> resolveExpression x identifierMap) expr
            match expr with
            | None -> Ok (Variable(uniqueName, None, storageClass), (identifierMap, blockSet, linkageSet))
            | Some (Error error) -> Error error
            | Some (Ok expr) -> Ok (Variable(uniqueName, Some expr, storageClass), (identifierMap, blockSet, linkageSet))
    
    if Set.contains ident scopeSet then
        let hasLinkage =
            Map.find ident identifierMap
            |> fun x -> Set.contains x linkageSet
        if not (hasLinkage && storageClass = Some Extern) then
            Error <| Message $"Duplicate local variable declaration of {ident}"
            else
                resolveVariable ()
    else
        resolveVariable ()
       
    
and resolveFunctionDeclaration (Function (name, parameters, body, storageClass)) (identifierMap, scopeSet, linkageSet) =
    let checkForDuplicate =
        if Map.containsKey name identifierMap then
            let hasLinkage = Set.contains name linkageSet
            if Set.contains name scopeSet && not hasLinkage then
                Error <| Message $"Duplicate declaration of {name}"
            else
                Ok ()
        else
            Ok ()
            
    let resolveParameter (identifierMap, paramSet) parameter =
        if Set.contains parameter paramSet then
            Error <| Message $"Duplicate parameter definition of {parameter}"
        else
            let tmp = Identifier (getTemporaryName ())
            let paramSet = Set.add parameter paramSet
            Ok (tmp, (Map.add parameter tmp identifierMap, paramSet))
            
    let rec resolveParameters state parameters acc =
        match parameters with
        | [] -> Ok (acc, state)
        | para :: rest ->
            let result = resolveParameter state para
            match result with
            | Error error -> Error error
            | Ok (resolvedPara, state) -> resolveParameters state rest (acc @ [resolvedPara])
    
    result {
        do! checkForDuplicate
        let identifierMap = Map.add name name identifierMap
        let scopeSet = Set.add name scopeSet
        let linkageSet = Set.add name linkageSet
        
        let! resolvedParameters, (newIdentifierMap, newScopeSet) = resolveParameters (identifierMap, Set.empty) parameters []
        
        let! resolvedBody =
            body
            |> Option.map (fun x -> resolveBlock x (newIdentifierMap, newScopeSet, linkageSet))
            |> Option.sequenceResult
        
        let newBody, linkageSet =
            match resolvedBody with
            | None -> None, linkageSet
            | Some (blck, linkageSet) -> Some blck, linkageSet 
        
        return Function (name, resolvedParameters, newBody, storageClass), (identifierMap, scopeSet, linkageSet)
    }
    
let resolveTopDeclarations declaration state =
    match declaration with
    // File Scope Variable Declaration
    | VariableDecl (Variable(identifier, _, _)) as decl ->
        let identifierMap, scopeSet, linkageSet = state
        let identifierMap = Map.add identifier identifier identifierMap
        let scopeSet = Set.add identifier scopeSet
        let linkageSet = Set.add identifier linkageSet
        Ok (decl, (identifierMap, scopeSet, linkageSet))
    | FunctionDecl functionDeclaration -> result {
        let! decl, state = resolveFunctionDeclaration functionDeclaration state
        return FunctionDecl decl, state
        }
    
let resolveProgram (Program declarations) =
    let rec resolveFile state decls acc =
        match decls with
        | [] -> Ok (acc, state)
        | func :: rest ->
            let result = resolveTopDeclarations func state
            match result with
            | Error error -> Error error
            | Ok (resolvedFunc, state) -> resolveFile state rest (acc @ [resolvedFunc])
    
    result {
        let! newDecl, state = resolveFile (Map.empty, Set.empty, Set.empty) declarations []
        let _, _, linkageSet = state
        return Program newDecl, linkageSet
    }

// ------------------------------------------------- Type Checking ---------------------------------------------------

type InitialValue =
    | Tentative
    | Initial of int
    | NoInitializer

type IdentifierAttributes =
    | FunAttr of defined: bool * globl: bool
    | StaticAttr of init: InitialValue * globl: bool
    | LocalAttr

type Symbol = {
        attribute: IdentifierAttributes
        sType: Type
    }

type SymbolTable = Map<Identifier, Symbol>

let getGlobalFromAttribute  attr =
    match attr with
    | FunAttr (_, globl) -> globl
    | StaticAttr (_, globl) -> globl
    | LocalAttr -> false

let rec typeCheckExpression symbolTable expr =
    let typeCheckExpressionList arg =
            arg
            |> Seq.map (typeCheckExpression symbolTable)
            |> Seq.sequenceResultM
            |> Result.map (Seq.iter (fun _ -> ()))
    
    match expr with
    | Var varName ->
        let symbol = Map.find varName symbolTable
        match symbol.sType with
        | Int -> Ok ()
        | _ -> Error <| Message $"Function '{varName}' used as variable"
    | FunctionCall (funcName, arguments) ->
        let symbol = Map.find funcName symbolTable
        match symbol.sType with
        | Int -> Error <| Message $"Variable '{funcName}' used as function"
        | FunType x when x = List.length arguments -> typeCheckExpressionList arguments
        | FunType _ -> Error <| Message $"Function '{funcName}' called with incorrect number of arguments"
    | Assignment(lvalue, rvalue) -> typeCheckExpressionList [lvalue; rvalue]
    | Unary(_, expression) -> typeCheckExpression symbolTable expression
    | Binary(_, left, right) -> typeCheckExpressionList [left; right]
    | Conditional(condition, middle, right) -> typeCheckExpressionList [condition; middle; right]
    | Constant _ -> Ok ()

let typeCheckOptionalExpression symbolTable optExpr =
    match optExpr with
    | None -> Ok ()
    | Some expr -> typeCheckExpression symbolTable expr

let rec typeCheckLocalVariableDeclaration symbolTable func  =
    let (Variable (name, init, storageClass)) = func

    match storageClass with
    | Some Extern -> result {
        do! if init.IsSome 
            then Error <| Message "Initializer on local extern variable declaration"
            else Ok ()

        let oldDecl = Map.tryFind name symbolTable
        match oldDecl with
        | Some {sType = t} when t <> Int -> return! Error <| Message "Function redeclared as variable"
        | Some _ -> return symbolTable
        | _ ->
            let attrs = StaticAttr(NoInitializer, true)
            return Map.add name {sType = Int; attribute = attrs} symbolTable
            
        }
    | Some Static -> result {
        let! initial =
            match init with
            | Some (Constant i) -> Ok (Initial i)
            | None -> Ok (Initial 0)
            | _ -> Error <| Message "Non-constant initializer on local static variable"
        
        let attrs = StaticAttr(initial, false)
        return Map.add name {sType = Int; attribute = attrs} symbolTable
        }
    | None -> result {
        let symbolTable = Map.add name {sType = Int; attribute = LocalAttr} symbolTable
        do! match init with
            | Some body -> typeCheckExpression symbolTable body
            | None -> Ok ()

        return symbolTable
        }
    

and typeCheckForInit symbolTable init =
    match init with
    | InitExpression None -> Ok symbolTable
    | InitExpression (Some expr) -> result {
        do! typeCheckExpression symbolTable expr
        return symbolTable
        }
    | InitDeclaration (Variable(_, _, storageClass) as varDecl) -> result {
        do! match storageClass with
            | Some _ -> Error <| Message "Variable declared inside a for-header cannot have a storage class specification"
            | None -> Ok ()
        let! symbolTable = typeCheckLocalVariableDeclaration symbolTable varDecl
        return symbolTable
        }

and typeCheckStatement symbolTable statement =
    match statement with
    | Return expr -> result {
        do! typeCheckExpression symbolTable expr
        return symbolTable
        }
    | Expression expression -> result {
        do! typeCheckExpression symbolTable expression
        return symbolTable
        }
    | If(condition, body, elseBody) -> result {
        do! typeCheckExpression symbolTable condition
        let! symbolTable = typeCheckStatement symbolTable body
        match elseBody with
        | None -> return symbolTable
        | Some elseStatement ->
            let! symbolTable = typeCheckStatement symbolTable elseStatement
            return symbolTable
        }
    | Label(_, statement) -> typeCheckStatement symbolTable statement
    | Compound block -> typeCheckBlock symbolTable block
    | DummyWhile(condition, body) -> result {
        do! typeCheckExpression symbolTable condition
        return! typeCheckStatement symbolTable body
        }
    | DummyDoWhile(body, condition) -> result {
        do! typeCheckExpression symbolTable condition
        return! typeCheckStatement symbolTable body
        }
    | DummyFor(forInit, condition, post, body) -> result {
        let! symbolTable = typeCheckForInit symbolTable forInit
        do! typeCheckOptionalExpression symbolTable condition
        do! typeCheckOptionalExpression symbolTable post
        return! typeCheckStatement symbolTable body
        }
    | DummySwitch(argument, body) -> result {
        do! typeCheckExpression symbolTable argument
        return! typeCheckStatement symbolTable body
        }
    | DummyCase(case, body) -> result {
        do! typeCheckExpression symbolTable case
        return! typeCheckStatement symbolTable body
        }
    | DummyDefault body -> typeCheckStatement symbolTable body
    
    | Goto _
    | DummyBreak
    | DummyContinue
    | Null -> Ok symbolTable
    
    | LoopBreak _
    | Continue _
    | While _
    | DoWhile _
    | For _ -> failwith "Loop labeling has to be performed after type checking"
    
    | Switch _
    | Case _
    | Default _
    | SwitchBreak _ -> failwith "Switch labeling has to be performed after type checking"

and typeCheckBlockItem symbolTable item =
    match item with
    | Declaration (VariableDecl var) -> result {
        let! symbolTable = typeCheckLocalVariableDeclaration symbolTable var
        return symbolTable
        }
    | Declaration (FunctionDecl func) -> typeCheckLocalFunctionDeclaration symbolTable func
    | Statement statement -> typeCheckStatement symbolTable statement
    
and typeCheckBlock symbolTable block =
    let rec loop state items =
        match items with
        | [] -> Ok state
        | item :: rest ->
            let checkedItem = typeCheckBlockItem state item
            match checkedItem with
            | Error error -> Error error
            | Ok state -> loop state rest
    
    loop symbolTable block

and typeCheckLocalFunctionDeclaration symbolMap func  =
    typeCheckFunctionDeclaration true symbolMap func

and typeCheckFileFunctionDeclaration symbolMap func =
    typeCheckFunctionDeclaration false symbolMap func

and typeCheckFunctionDeclaration inBlock (symbolTable: Map<Identifier,Symbol>) func=
    let (Function (name, parameters, body, storageClass)) = func
    
    let funcType = FunType <| List.length parameters
    let globl = storageClass <> Some Static

    let getOldEntry =
        if Map.containsKey name symbolTable then
            let oldEntry = Map.find name symbolTable
            if oldEntry.sType <> funcType then
                Error <| Message $"Incompatible function declaration for function '{name}'\nOld type: {oldEntry.sType}\nnewType: {funcType}"
            else
            let alreadyDefined =
                match oldEntry.attribute with
                | FunAttr (defined, _) -> defined
                | _ -> false
            if alreadyDefined && Option.isSome body then
                Error <| Message $"Multiple definitions for function '{name}'"
            else Ok ((Some oldEntry), alreadyDefined)
        else Ok (None, false)
        
    result {
        // Check if static storage class in block
        do! if inBlock && storageClass = Some Static
            then Error <| Message "Static function declarations are not allowed in block-scopes"
            else Ok ()
        
        let! oldEntry, alreadyDefined = getOldEntry
        let! globl =
            match oldEntry with
            | None -> Ok globl
            | Some entry ->
                let oldGlobl = getGlobalFromAttribute entry.attribute
                if oldGlobl && storageClass = Some Static
                then Error <| Message "Static function declaration follows non-static"
                else Ok oldGlobl
        
        let defined =
            match body with
            | None -> false
            | Some _ -> true
        let attrs = FunAttr(defined || alreadyDefined, globl)
        let symbolTable = Map.add name { attribute = attrs; sType = funcType} symbolTable
        
        let registerParameter state parameter =
            Map.add parameter {sType = Int; attribute = LocalAttr } state
        let symbolTable = List.fold registerParameter symbolTable parameters
            
        match body with
        | None -> return symbolTable
        | Some block ->
            let! symbolTable = typeCheckBlock symbolTable block
            return symbolTable
    }

let typeCheckFileVariableDeclaration symbolTable declaration =
    let (Variable (ident, init, storageClass)) = declaration
    let initializer () = 
        match init with
        | Some (Constant i) -> Ok <| Initial i
        | None ->
            if storageClass = Some Extern
            then Ok NoInitializer
            else Ok Tentative
        | _ -> Error <| Message "Non-constant initializer"
    
    let globl = storageClass <> Some Static
    
    if Map.containsKey ident symbolTable then
        let oldDecl = Map.find ident symbolTable
        result {
            do! if oldDecl.sType <> Int
                then Error <| Message "Hello"
                else Ok ()
                                
            let oldGlobl =
                match oldDecl.attribute with
                | FunAttr (_, globl) -> globl
                | StaticAttr (_, globl) -> globl
                | _ -> globl
            
            let! newGlobl =
                if storageClass = Some Extern then Ok oldGlobl
                // Something is going wrong here.
                // This should be uncommented to catch potential errors.
                // But doing so makes a test case fail.
                // TODO: look into this? Or maybe this is fine?
                else if oldGlobl <> globl then Error <| Message "Conflicting variable linkage"
                else Ok globl
            
            let! initialValue =
                match oldDecl.attribute with
                | StaticAttr (Initial i, _) ->
                    match init with
                    | Some (Constant _) -> Error <| Message "Conflicting file scope variable definitions"
                    | _ -> Ok (Initial i)
                | _ -> Ok Tentative
        
            let attrs = StaticAttr (initialValue, newGlobl)
            return Map.add ident {oldDecl with attribute = attrs; sType = Int} symbolTable
        }
    else
        result {
            let! initialValue = initializer ()
            let attrs = StaticAttr (initialValue, globl)
            return Map.add ident {attribute = attrs; sType = Int;} symbolTable
        }


let rec typeCheckFileDeclaration symbolTable declaration =
    match declaration with
    | VariableDecl decl -> typeCheckFileVariableDeclaration symbolTable decl
    | FunctionDecl decl -> typeCheckFileFunctionDeclaration symbolTable decl

let typeCheckProgram (Program functions) =
    let rec loop state functions =
        match functions with
        | [] -> Ok state
        | func :: rest ->
            let checkedFunction = typeCheckFileDeclaration state func
            match checkedFunction with
            | Error error -> Error error
            | Ok state -> loop state rest
            
    loop Map.empty functions

// ---------------------------------------------- Resolve Goto Labels ------------------------------------------------

(*
    All the in C defined goto labels need to be converted to globally unique labels.
    To achieve this, we need track a state as we resolve the new label names.
    Labels and gotos work only inside a function; meaning for each function a new state is used.
    The state has the following members:
    - labelMap: A map from in C defined labels to globally unique labels
    - labelSet: A set that tracks all defined labels, in order to detect labels with multiple definitions
*)

let rec resolveGotoStatement statement (labelMap, labelSet) =
    let state = (labelMap, labelSet)
    match statement with
    | Goto name ->
        if Map.containsKey name labelMap then
            let tmpLabel = Map.find name labelMap
            Ok (Goto tmpLabel, (labelMap, labelSet))
        else
            let tmpLabel = getGotoLabel ()
            let labelMap = Map.add name tmpLabel labelMap
            Ok (Goto tmpLabel, (labelMap, labelSet))
    | Label (name, labelStatement) -> result {
        let! resolvedStatement, (labelMap, labelSet) = resolveGotoStatement labelStatement (labelMap, labelSet)
        if Map.containsKey name labelMap then
            if Set.contains name labelSet then
                return! Error <| Message $"Label {name} has been defined multiple times"
            else
                let tmpLabel = Map.find name labelMap
                let labelSet = Set.add name labelSet
                return Label (tmpLabel, resolvedStatement), (labelMap, labelSet)
        else
            let tmpLabel = getGotoLabel ()
            let labelMap = Map.add name tmpLabel labelMap
            let labelSet = Set.add name labelSet
            return Label (tmpLabel, resolvedStatement), (labelMap, labelSet)
        }
    | If (cond, ifStatement, elseOpt) -> result {
        let! resolvedIf, state = resolveGotoStatement ifStatement (labelMap, labelSet)
        match elseOpt with
        | None -> return If (cond, resolvedIf, None), state
        | Some elseStatement ->
            let! resolvedElse, state = resolveGotoStatement elseStatement state
            return If (cond, resolvedIf, Some resolvedElse), state
        }
    | Return _
    | Expression _ 
    | Null -> Ok (statement, (labelMap, labelSet))
    | Compound block -> result {
        let! newBlock, state = resolveGotoBlock block (labelMap, labelSet)
        return Compound newBlock, state
        }
    | DummyBreak -> Ok (statement, state)
    | DummyContinue -> Ok (statement, state)
    | DummyWhile(cond, body) -> result {
        let! resolvedBody, state = resolveGotoStatement body state
        return DummyWhile (cond, resolvedBody), state
        }
    | DummyDoWhile(body, cond) -> result {
        let! resolvedBody, state = resolveGotoStatement body state
        return DummyDoWhile (resolvedBody, cond), state
        }
    | DummyFor(init, cond, post, body) -> result {
        let! resolvedBody, state = resolveGotoStatement body state
        return DummyFor (init, cond, post, resolvedBody), state
        }
    | DummySwitch (argument, body) -> result {
        let! resolvedBody, state = resolveGotoStatement body state
        return DummySwitch (argument, resolvedBody), state
        }
    | DummyCase(expression, body) -> result {
        let! resolvedBody, state = resolveGotoStatement body state
        return DummyCase (expression, resolvedBody), state
        }
    | DummyDefault body -> result {
        let! resolvedBody, state = resolveGotoStatement body state
        return DummyDefault resolvedBody, state
        } 
    
    | LoopBreak _
    | Continue _
    | While _
    | DoWhile _
    | For _ -> failwith "Goto resolution needs to be performed before loop labeling"
    
    | Switch _
    | Case _
    | Default _
    | SwitchBreak _ -> failwith "Goto resolution needs to be performed before switch labeling"

and resolveGotoBlock items state =
    let rec resolve state item =
        match item with
        | Statement statement ->
            let resolvedStatement = resolveGotoStatement statement state
            match resolvedStatement with
            | Error error -> Error error, state
            | Ok (newStatement, state) -> Ok (Statement newStatement), state
        | _ -> Ok item, state
    
    let resultSeq, newState = Seq.mapFold resolve state items
    let result =
        resultSeq
        |> Seq.sequenceResultM
        |> Result.map Array.toList
    match result with
    | Error error -> Error error
    | Ok block -> Ok (block, newState)

let resolveGotoFunction (Function(name, parameters, body, storageClass)) =
    match body with
    | None -> Ok (Function (name, parameters, None, storageClass))
    | Some block -> result {
        let emptyState = (Map.empty, Set.empty)
        let! resolvedBlock, _ = resolveGotoBlock block emptyState
        return Function (name, parameters, Some resolvedBlock, storageClass)
        }

let resolveGotoTopDeclarations declaration =
    match declaration with
    | VariableDecl _ -> Ok declaration
    | FunctionDecl func ->
        resolveGotoFunction func
        |> Result.map FunctionDecl

let rec resolveGotoProgram (Program functions) =
    functions
    |> Seq.map resolveGotoTopDeclarations
    |> Seq.sequenceResultM
    |> Result.map Array.toList
    |> Result.map Program

// ------------------------------------- Switch Labeling -----------------------------------------------------------

(*
    For codgen all switch statements including case statements and default statements need to be labeled.
    The state, that needs to be tracked is:
    - currentSwitch: Tracks the label of the current switch we are inside (if we are indeed inside a switch statement at all)
    - inLoop: Tracks if switched inside a loop; break statements inside a loop belong to the loop and not the switch, so those get ignored in this step
    - cases: We collect a set of case statements for the current switch in the form (label, expression)
    - defaults: We collect a list of all default statements for the current switch and their labels 
*)

type SwitchResolutionState = SwitchState of currentSwitch: Identifier option * cases: (Identifier * Expression) list * defaults: Expression list

let rec resolveSwitchStatement statement (currentSwitch, inLoop, cases, defaults) =
    match statement with
    | DummyCase (Constant value, body) ->
        match currentSwitch with
        | None -> Error <| Message "Case statement outside of switch"
        | Some _ -> result {
            let expression = Constant value
            let caseLabel = getSwitchLabel ()
            let pair = (caseLabel, expression)
            let! resolvedBody, (cases, defaults) = resolveSwitchStatement body (currentSwitch, inLoop, cases, defaults)
            let thisCase = Case (caseLabel, resolvedBody)
            let allCaseExpressions =
                cases
                |> Seq.map snd
                
            if Seq.contains expression allCaseExpressions then
                return! Error <| Message $"Duplicate case statement of {expression}"
            else
                let cases = Set.add pair cases
                return (thisCase, (cases, defaults))
            }
    | DummyCase (nonConstant, _) -> Error <| Message $"Non-Constant case statement {nonConstant}"
    | DummyDefault body ->
        match currentSwitch with
        | None -> Error <| Message "Default statement outside of switch"
        | Some _ -> result {
            let defaultLabel = getSwitchLabel ()
            let! resolvedBody, (cases, defaults) = resolveSwitchStatement body (currentSwitch, inLoop, cases, defaults)
            let thisDefault = Default (defaultLabel, resolvedBody)
            return (thisDefault, (cases, defaults @ [Identifier defaultLabel]))
            }
    | DummySwitch(argument, body) -> result {
        let label = getSwitchLabel ()
        let! resolvedBody, (thisCases, thisDefaults) = resolveSwitchStatement body (Some label, false, Set.empty, List.empty)
        if (List.length thisDefaults) > 1 then
            return! Error <| Message "More than one default statement in switch statement"
        else
            let defaultCase = List.tryHead thisDefaults
            return Switch (argument, resolvedBody, thisCases, defaultCase, label), (cases, defaults)
        }
    | If (condition, body, elseOption) -> result {
        let! resolvedBody, (cases, defaults) = resolveSwitchStatement body (currentSwitch, inLoop, cases, defaults)
        match elseOption with
        | None -> return If (condition, resolvedBody, None), (cases, defaults)
        | Some elseBody ->
            let! resolvedElse, (cases, defaults) = resolveSwitchStatement elseBody (currentSwitch, inLoop, cases, defaults)
            return If (condition, resolvedBody, Some resolvedElse), (cases, defaults)
        }
    | Label(name, statement) -> result {
        let! resolvedStatement, (cases, defaults) = resolveSwitchStatement statement (currentSwitch, inLoop, cases, defaults)
        return Label (name, resolvedStatement), (cases, defaults)
        }
    | DummyBreak ->
        match currentSwitch with
        | None -> Ok (DummyBreak, (cases, defaults))
        | Some label ->
            if inLoop then Ok (DummyBreak, (cases, defaults))
            else Ok (SwitchBreak label, (cases, defaults))
    | DummyWhile (condition, body) -> result {
        let! resolvedBody, (cases, defaults) = resolveSwitchStatement body (currentSwitch, true, cases, defaults)
        return DummyWhile (condition, resolvedBody), (cases, defaults)
        }
    | DummyDoWhile(body, condition) -> result {
        let! resolvedBody, (cases, defaults) = resolveSwitchStatement body (currentSwitch, true, cases, defaults)
        return DummyDoWhile (resolvedBody, condition), (cases, defaults)
        }
    | DummyFor(forInit, condition, post, body) -> result {
        let! resolvedBody, (cases, defaults) = resolveSwitchStatement body (currentSwitch, true, cases, defaults)
        return DummyFor (forInit, condition, post, resolvedBody), (cases, defaults)
        }
    | Compound block -> result {
        let! resolvedBlock, (cases, defaults) = resolveSwitchBlock block (currentSwitch, inLoop, cases, defaults)
        return Compound resolvedBlock, (cases, defaults)
        }

    | Null
    | Expression _
    | Goto _
    | DummyContinue
    | Return _ -> Ok (statement, (cases, defaults))
    
    | LoopBreak _
    | Continue _
    | While _
    | DoWhile _
    | For _ -> failwith "Switch labeling needs to be performed before loop labeling"
    
    | Switch _
    | Case _
    | Default _
    | SwitchBreak _ -> failwith "Switch labeling has already been done"
    
and resolveSwitchBlockItem item (currentSwitch, inLoop, cases, defaults) =
    match item with
    | Statement statement -> result {
        let! resolvedStatement, (cases, defaults) = resolveSwitchStatement statement (currentSwitch, inLoop, cases, defaults)
        return Statement resolvedStatement, (cases, defaults)
        }
    | Declaration _ -> Ok (item, (cases, defaults))
    
and resolveSwitchBlock block (currentSwitch, inLoop, cases, defaults) =
    let rec loop (cases, defaults) items acc =
        match items with
        | item :: rest ->
            let resolveResult = resolveSwitchBlockItem item (currentSwitch, inLoop, cases, defaults)
            match resolveResult with
            | Error error -> Error error
            | Ok (resolvedItem, (cases, defaults)) -> loop (cases, defaults) rest (acc @ [resolvedItem])
        | [] -> Ok (acc, (cases, defaults))
    
    loop (cases, defaults) block []

let resolveSwitchFunction (Function(name, parameters, body, StorageClass)) =
    match body with
    | None -> Ok (Function (name, parameters, None, StorageClass))
    | Some block -> result {
        let! resolvedBody, _ = resolveSwitchBlock block (None, false, Set.empty, List.empty)
        return Function (name, parameters, Some resolvedBody, StorageClass)
        }

let resolveSwitchTopDeclarations declaration =
    match declaration with
    | VariableDecl _ -> Ok declaration
    | FunctionDecl func ->
        resolveSwitchFunction func
        |> Result.map FunctionDecl

let resolveSwitchProgram (Program functions) =
    functions
    |> Seq.map resolveSwitchTopDeclarations
    |> Seq.sequenceResultM
    |> Result.map Array.toList
    |> Result.map Program

// --------------------------------------- Loop Labeling -----------------------------------------------------------

(*
    All loops need to be given a label for codegen.
    Here only the current label needs to be tracked as state
    - currentLabel: tracks the label of the current loop
*)

let rec resolveLoopStatement statement currentLabel =
     match statement with
     | DummyBreak ->
         match currentLabel with
         | Some label -> Ok (LoopBreak label)
         | None -> Error <| Message "Break statement outside of loop"
     | DummyContinue ->
         match currentLabel with
         | Some label -> Ok (Continue label)
         | None -> Error <| Message "Continue statement outside of loop"
     | DummyWhile (cond, body) -> result {
        let newLabel = getLoopLabel ()
        let! resolvedBody = resolveLoopStatement body (Some newLabel)
        return While(cond, resolvedBody, newLabel)
        }
     | DummyDoWhile (body, cond) -> result {
        let newLabel = getLoopLabel ()
        let! resolvedBody = resolveLoopStatement body (Some newLabel)
        return DoWhile(resolvedBody, cond, newLabel)
        }
     | DummyFor (init, cond, post, body) -> result {
        let newLabel = getLoopLabel ()
        let! resolvedBody = resolveLoopStatement body (Some newLabel)
        return For(init, cond, post, resolvedBody, newLabel)
        }
     | Label (name, labelStatement) -> result {
        let! resolvedStatement = resolveLoopStatement labelStatement currentLabel
        return Label (name, resolvedStatement)
        }
     | Compound block -> result {
        let! resolvedBlock = resolveLoopBlock block currentLabel
        return Compound resolvedBlock
        }
     | If (cond, body, elseBody) -> result {
        let! resolvedBody = resolveLoopStatement body currentLabel
        let! resolvedElse =
            elseBody
            |> Option.map (fun x -> resolveLoopStatement x currentLabel)
            |> Option.sequenceResult
        return If (cond, resolvedBody, resolvedElse)
        }
     | Switch(argument, body, cases, defaultCase, label) -> result {
        let! resolvedBody = resolveLoopStatement body currentLabel
        return Switch (argument, resolvedBody, cases, defaultCase, label)
        }
     | Case (label, body) -> result {
        let! resolvedBody = resolveLoopStatement body currentLabel
        return Case (label, resolvedBody)
        }
     | Default (label, body) -> result {
        let! resolvedBody = resolveLoopStatement body currentLabel
        return Default (label, resolvedBody)
        }
     
     | Expression _
     | Goto _
     | Null
     | SwitchBreak _
     | Return _ -> Ok statement
     
     | LoopBreak _
     | Continue _
     | While _
     | DoWhile _
     | For _ -> failwith "Loop labeling has already been done"
     
     | DummySwitch _
     | DummyCase _
     | DummyDefault _ -> failwith "Loop labeling has to be done after switch labeling"

and resolveLoopBlockItem currentLabel item =
    match item with
    | Statement statement -> Result.map Statement (resolveLoopStatement statement currentLabel)
    | Declaration _ -> Ok item

and resolveLoopBlock block currentLabel =
   block
   |> Seq.map (resolveLoopBlockItem currentLabel)
   |> Seq.sequenceResultM
   |> Result.map Array.toList

let resolveLoopFunction (Function(name, parameters, body, storageClass)) =
    match body with
    | None -> Ok (Function (name, parameters, None, storageClass))
    | Some block -> result {
        let! resolvedBody = resolveLoopBlock block None
        return Function (name, parameters, Some resolvedBody, storageClass)
        }

let resolveLoopTopDeclaration declaration =
    match declaration with
    | VariableDecl _ -> Ok declaration
    | FunctionDecl func ->
        resolveLoopFunction func
        |> Result.map FunctionDecl

let resolveLoopProgram (Program functions) =
    functions
    |> Seq.map resolveLoopTopDeclaration
    |> Seq.sequenceResultM
    |> Result.map Array.toList
    |> Result.map Program

// ------------------------------- Complete Semantic Analysis ------------------------------------------------------

let semanticAnalysis program=
    result {
        let! program, linkageSet = resolveProgram program
        let! symbolTable = typeCheckProgram program

        let! program = 
            program
            |> resolveGotoProgram
            |> Result.bind resolveSwitchProgram
            |> Result.bind resolveLoopProgram 

        return program, (symbolTable, linkageSet)
        }
    
    