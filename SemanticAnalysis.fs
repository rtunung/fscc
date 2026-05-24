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

let resolveDeclaration (ident, expr) (variableMap:Map<Identifier,Identifier>) =
    if Map.containsKey ident variableMap then
        Error <| Message $"Duplicate variable declaration of {ident}"
    else
        let uniqueName = Identifier (getTemporaryName ())
        let variableMap = Map.add ident uniqueName variableMap

        let expr = Option.map (fun x -> resolveExpression x variableMap) expr
        match expr with
        | None -> Ok (Declaration (uniqueName, None), variableMap)
        | Some (Error error) -> Error error
        | Some (Ok expr) -> Ok (Declaration (uniqueName, Some expr), variableMap)

let rec resolveStatement statement variableMap =
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
        let! ifBody = resolveStatement ifBody variableMap
        match elseBody with
        | None -> return If (cond, ifBody, None)
        | Some elseBody ->
            let! elseBody = resolveStatement elseBody variableMap
            return If (cond, ifBody, Some elseBody)
            }
    | Label (name, labelStatement) -> result {
        let! labelStatement = resolveStatement labelStatement variableMap
        return Label (name, labelStatement)
        }
    | Goto _ -> Ok statement

let rec resolveBlockItem item variableMap =
    match item with
    | Declaration declaration -> resolveDeclaration declaration variableMap
    | Statement statement -> result {
        let! statement = resolveStatement statement variableMap
        return Statement statement, variableMap
        }
    
let resolveBlockItems items variableMap =
    let rec loop items variableMap acc =
        match items with
        | [] -> Ok acc
        | item :: rest ->
            let resolvedItem = resolveBlockItem item variableMap
            match resolvedItem with
            | Error error -> Error error
            | Ok (newItem, variableMap) -> loop rest variableMap (acc @ [newItem])
    
    loop items variableMap []
    
let resolveFunction variableMap (Function(funcName, blockItems)) = result {
    let! resolvedItem = resolveBlockItems blockItems variableMap
    return Function (funcName, resolvedItem)
    }

// ---------------------------------------------- Resolve Goto Labels ------------------------------------------------

let rec resolveGotoStatement statement (labelMap, labelSet) =
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


// TODO: Once we have compound Statements, then this function will also have to return the state back to resolveGotoFunction
let resolveGotoBlockItems items state =
    let rec resolve state item =
        match item with
        | Statement statement ->
            let resolvedStatement = resolveGotoStatement statement state
            match resolvedStatement with
            | Error error -> Error error, state
            | Ok (newStatement, state) -> Ok (Statement newStatement), state
        | _ -> Ok item, state
    
    items
    |> Seq.mapFold resolve state
    |> fst
    |> Seq.sequenceResultM
    |> Result.map Array.toList

let resolveGotoFunction (Function(funcName, blockItems)) = result {
    let emptyState = (Map.empty, Set.empty)
    let! newBlockItems = resolveGotoBlockItems blockItems emptyState
    return Function (funcName, newBlockItems)
    }

// ------------------------------- Complete Semantic Analysis ------------------------------------------------------

let semanticAnalysis (Program func) =
    let newMap = Map.empty
    func
    |> resolveFunction newMap
    |> Result.bind resolveGotoFunction
    |> Result.map Program
    