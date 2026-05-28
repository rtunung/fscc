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

// ------------------------------------- Resolve Variable Identifiers --------------------------------------------------

(*
    The variable names need to be mapped to globally unique names.
    To achieve this, we need track a state as we resolve the new variables names.
    The state has the following members:
    - variableMap: A map from in C defined variable identifiers to globally unique identifiers
    - blockSet: A set that contains all variables that are declared in the current block (Does not include parent or child blocks)
        -> Detect multiple declarations in the same block.
        -> Allows for shadowing of variable identifiers once you go into a child block
*)

let rec resolveExpression expr (variableMap:Map<Identifier, Identifier>) =
    match expr with
    | Assignment (Var left, right) -> result {
        let! left = resolveExpression (Var left) variableMap
        let! right = resolveExpression right variableMap
        return Assignment (left, right)
        }
    | Assignment (invalid, _) -> Error <| Message $"Invalid lvalue {invalid}"
    | Var name when Map.containsKey name variableMap ->
        let uniqueName = Map.find name variableMap
        Ok (Var uniqueName)
    | Var undeclared -> Error <| Message $"Variable {undeclared} is undeclared"
    | Constant _ -> Ok expr
    | Unary (inc, Var a) when isIncrementDecrement inc -> result {
        let! expr = resolveExpression (Var a) variableMap
        return Unary (inc, expr)
        }
    | Unary (inc, invalid) when isIncrementDecrement inc -> Error <| Message $"Invalid lvalue {invalid} for operator {inc}"
    | Unary(operator, expression) -> result {
        let! expression = resolveExpression expression variableMap
        return Unary(operator, expression)
        }
    | Binary(operator, left, right) -> result {
        let! left = resolveExpression left variableMap
        let! right = resolveExpression right variableMap
        return Binary(operator, left, right)
        }
    | Conditional(cond, middle, right) -> result {
        let! cond = resolveExpression cond variableMap
        let! middle = resolveExpression middle variableMap
        let! right = resolveExpression right variableMap
        return Conditional(cond, middle, right)
        }

let resolveDeclaration (ident, expr) (variableMap, blockSet) =
    if Set.contains ident blockSet then
        Error <| Message $"Duplicate variable declaration of {ident}"
    else
        let uniqueName = Identifier (getTemporaryName ())
        let variableMap = Map.add ident uniqueName variableMap
        let blockSet = Set.add ident blockSet

        let expr = Option.map (fun x -> resolveExpression x variableMap) expr
        match expr with
        | None -> Ok (((uniqueName, None):Declaration), (variableMap, blockSet))
        | Some (Error error) -> Error error
        | Some (Ok expr) -> Ok ((uniqueName, Some expr), (variableMap, blockSet))

let rec resolveStatement statement (variableMap, blockSet) =
    match statement with
    | Null -> Ok Null
    | Return expr -> result {
        let! expr = resolveExpression expr variableMap
        return Return expr
        }
    | Expression expr ->  result {
        let! expr = resolveExpression expr variableMap
        return Expression expr
        }
    | If (cond, ifBody, elseBody) -> result {
        let! cond = resolveExpression cond variableMap
        let! ifBody = resolveStatement ifBody (variableMap,blockSet)
        match elseBody with
        | None -> return If (cond, ifBody, None)
        | Some elseBody ->
            let! elseBody = resolveStatement elseBody (variableMap, blockSet)
            return If (cond, ifBody, Some elseBody)
            }
    | Label (name, labelStatement) -> result {
        let! labelStatement = resolveStatement labelStatement (variableMap, blockSet)
        return Label (name, labelStatement)
        }
    | Goto _ -> Ok statement
    | Compound block ->  result {
        let! newBlock = resolveBlock block variableMap
        return Compound newBlock
        }
    | DummyBreak -> Ok statement
    | DummyContinue -> Ok statement
    | DummyWhile(cond, body) -> result {
        let! resolvedCond = resolveExpression cond variableMap
        let! resolvedBody = resolveStatement body (variableMap, blockSet)
        return DummyWhile (resolvedCond, resolvedBody)
        }
    | DummyDoWhile(body, cond) -> result {
        let! resolvedBody = resolveStatement body (variableMap, blockSet)
        let! resolvedCond = resolveExpression cond variableMap
        return DummyDoWhile (resolvedBody, resolvedCond)
        }
    | DummyFor(init, cond, post, body) -> result {
        let! resolvedInit, (variableMap, blockSet) = resolveForInit init variableMap
        let! resolvedCond = resolveOptionalExpression cond variableMap
        let! resolvedPost = resolveOptionalExpression post variableMap
        let! resolvedBody = resolveStatement body (variableMap, blockSet)
        return DummyFor (resolvedInit, resolvedCond, resolvedPost, resolvedBody)
        }
    
    | Break _
    | Continue _
    | DoWhile _
    | For _ 
    | While _ -> failwith "Variable resolution needs to be performed before loop labeling"
    
    
and resolveOptionalExpression expr variableMap =
    expr
    |> Option.map (fun x ->  resolveExpression x variableMap)
    |> Option.sequenceResult
    
and resolveForInit init variableMap=
    match init with
    | InitExpression None -> Ok (InitExpression None, (variableMap, Set.empty))
    | InitExpression (Some expr) -> result {
        let! resolvedExpr = resolveExpression expr variableMap
        return InitExpression (Some resolvedExpr), (variableMap, Set.empty)
        }
    | InitDeclaration declaration -> result {
        let! resolvedDecl, state = resolveDeclaration declaration (variableMap, Set.empty)
        return InitDeclaration resolvedDecl, state
        }

and resolveBlockItem item (variableMap, blockSet) =
    match item with
    | Declaration declaration -> result {
        let! resolvedDecl, state = resolveDeclaration declaration (variableMap, blockSet)
        return Declaration resolvedDecl, state
        }
    | Statement statement -> result {
        let! statement = resolveStatement statement (variableMap, blockSet)
        return Statement statement, (variableMap, blockSet)
        }
    
and resolveBlock items variableMap =
    let rec loop items (variableMap, blockSet) acc =
        match items with
        | [] -> Ok acc
        | item :: rest ->
            let resolvedItem = resolveBlockItem item (variableMap, blockSet)
            match resolvedItem with
            | Error error -> Error error
            | Ok (newItem, (variableMap, blockSet)) -> loop rest (variableMap, blockSet) (acc @ [newItem])
    
    loop items (variableMap, Set.empty) []
    
let resolveFunction variableMap (Function(funcName, blockItems)) = result {
    let! resolvedItem = resolveBlock blockItems variableMap
    return Function (funcName, resolvedItem)
    }

// ---------------------------------------------- Resolve Goto Labels ------------------------------------------------

(*
    All the in C defined goto labels need to be converted to globally unique labels.
    To achieve this, we need track a state as we resolve the new label names.
    Labels and gotos work only inside a function; meaning for each function a new state is used.
    The state has the following members:
    - labelMap: A map from in C defiend labels to globally uninque labels
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
    
    | Break _
    | Continue _
    | While _
    | DoWhile _
    | For _ -> failwith "Goto resolution needs to be performed before loop labeling"

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

let resolveGotoFunction (Function(funcName, blockItems)) = result {
    let emptyState = (Map.empty, Set.empty)
    let! newBlockItems, _ = resolveGotoBlock blockItems emptyState
    return Function (funcName, newBlockItems)
    }

// --------------------------------------- Loop Labeling -----------------------------------------------------------

let rec resolveLoopStatement statement currentLabel =
    match statement with
     | DummyBreak ->
         match currentLabel with
         | Some label -> Ok (Break label)
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
     
     | Expression _
     | Goto _
     | Null
     | Return _ -> Ok statement
     
     | Break _
     | Continue _
     | While _
     | DoWhile _
     | For _ -> failwith "Loop labeling has already been done"


and resolveLoopBlockItem currentLabel item =
    match item with
    | Statement statement -> Result.map Statement (resolveLoopStatement statement currentLabel)
    | Declaration _ -> Ok item

and resolveLoopBlock block currentLabel =
   block
   |> Seq.map (resolveLoopBlockItem currentLabel)
   |> Seq.sequenceResultM
   |> Result.map Array.toList

let resolveLoopFunction (Function(name, body)) = result {
    let! resolvedBody = resolveLoopBlock body None
    return Function (name, resolvedBody)
    }

// ------------------------------- Complete Semantic Analysis ------------------------------------------------------

let semanticAnalysis (Program func) =
    let newMap = Map.empty
    func
    |> resolveFunction newMap
    |> Result.bind resolveGotoFunction
    |> Result.bind resolveLoopFunction
    |> Result.map Program
    