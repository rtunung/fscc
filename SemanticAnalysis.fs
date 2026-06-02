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
    - identifierMap: A map from in C defined variable identifiers to globally unique identifiers
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
    | Null -> Ok Null
    | Return expr -> result {
        let! expr = resolveExpression expr identifierMap
        return Return expr
        }
    | Expression expr ->  result {
        let! expr = resolveExpression expr identifierMap
        return Expression expr
        }
    | If (cond, ifBody, elseBody) -> result {
        let! cond = resolveExpression cond identifierMap
        let! ifBody = resolveStatement ifBody (identifierMap, scopeSet, linkageSet)
        match elseBody with
        | None -> return If (cond, ifBody, None)
        | Some elseBody ->
            let! elseBody = resolveStatement elseBody (identifierMap, scopeSet, linkageSet)
            return If (cond, ifBody, Some elseBody)
            }
    | Label (name, labelStatement) -> result {
        let! labelStatement = resolveStatement labelStatement (identifierMap, scopeSet, linkageSet)
        return Label (name, labelStatement)
        }
    | Goto _ -> Ok statement
    | Compound block ->  result {
        let! newBlock = resolveBlock block (identifierMap, Set.empty, linkageSet)
        return Compound newBlock
        }
    | DummyBreak -> Ok statement
    | DummyContinue -> Ok statement
    | DummyWhile(cond, body) -> result {
        let! resolvedCond = resolveExpression cond identifierMap
        let! resolvedBody = resolveStatement body (identifierMap, scopeSet, linkageSet)
        return DummyWhile (resolvedCond, resolvedBody)
        }
    | DummyDoWhile(body, cond) -> result {
        let! resolvedBody = resolveStatement body (identifierMap, scopeSet, linkageSet)
        let! resolvedCond = resolveExpression cond identifierMap
        return DummyDoWhile (resolvedBody, resolvedCond)
        }
    | DummyFor(init, cond, post, body) -> result {
        let! resolvedInit, (identifierMap, scopeSet, linkageSet) = resolveForInit init (identifierMap, linkageSet)
        let! resolvedCond = resolveOptionalExpression cond identifierMap
        let! resolvedPost = resolveOptionalExpression post identifierMap
        let! resolvedBody = resolveStatement body (identifierMap, scopeSet, linkageSet)
        return DummyFor (resolvedInit, resolvedCond, resolvedPost, resolvedBody)
        }
    | DummySwitch (argument, body) -> result {
        let! resolvedArgument = resolveExpression argument identifierMap
        let! resolvedBody = resolveStatement body (identifierMap, scopeSet, linkageSet)
        return DummySwitch (resolvedArgument,  resolvedBody)
        }
    | DummyCase (case, body) -> result {
        let! resolvedCase = resolveExpression case identifierMap
        let! resolvedBody = resolveStatement body (identifierMap, scopeSet, linkageSet)
        return DummyCase (resolvedCase, resolvedBody)
        }
    | DummyDefault body -> result {
        let! resolvedBody = resolveStatement body (identifierMap, scopeSet, linkageSet)
        return DummyDefault resolvedBody
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
        let! resolvedDecl, state = resolveVariableDeclaration declaration (identifierMap, Set.empty, linkageSet)
        return InitDeclaration resolvedDecl, state
        }

and resolveBlockItem item (identifierMap, scopeSet, linkageSet) =
    match item with
    | Declaration (VariableDecl declaration) -> result {
        let! resolvedDecl, state = resolveVariableDeclaration declaration (identifierMap, scopeSet, linkageSet)
        return Declaration (VariableDecl resolvedDecl), state
        }
    | Declaration (FunctionDecl (Function (_, _, None) as func)) -> result {
        let! resolvedFunc, state = resolveFunctionDeclaration func (identifierMap, scopeSet, linkageSet)
        return Declaration (FunctionDecl resolvedFunc), state
        }
    | Declaration (FunctionDecl (Function (name, _, _))) -> Error <| Message $"Nested function definition are invalid. Function: {name}" 
    | Statement statement -> result {
        let! statement = resolveStatement statement (identifierMap, scopeSet, linkageSet)
        return Statement statement, (identifierMap, scopeSet, linkageSet)
        }
    
and resolveBlock items (identifierMap, scopeSet, linkageSet) =
    let rec loop items (identifierMap, scopeSet, linkageSet) acc =
        match items with
        | [] -> Ok acc
        | item :: rest ->
            let resolvedItem = resolveBlockItem item (identifierMap, scopeSet, linkageSet)
            match resolvedItem with
            | Error error -> Error error
            | Ok (newItem, (variableMap, scopeSet, linkageSet)) -> loop rest (variableMap, scopeSet, linkageSet) (acc @ [newItem])
    
    loop items (identifierMap, scopeSet, linkageSet) []
   
and resolveVariableDeclaration (Variable (ident, expr)) (identifierMap, scopeSet, linkageSet) =
    if Set.contains ident scopeSet then
        Error <| Message $"Duplicate variable declaration of {ident}"
    else
        let uniqueName = Identifier (getTemporaryName ())
        let identifierMap = Map.add ident uniqueName identifierMap
        let blockSet = Set.add ident scopeSet

        let expr = Option.map (fun x -> resolveExpression x identifierMap) expr
        match expr with
        | None -> Ok (Variable(uniqueName, None), (identifierMap, blockSet, linkageSet))
        | Some (Error error) -> Error error
        | Some (Ok expr) -> Ok (Variable(uniqueName, Some expr), (identifierMap, blockSet, linkageSet))
    
and resolveFunctionDeclaration (Function (name, parameters, body)) (identifierMap, scopeSet, linkageSet) =
    let checkForDuplicate =
        if Map.containsKey name identifierMap then
            if Set.contains name scopeSet && not (Set.contains name linkageSet) then
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
        let! () = checkForDuplicate
        let identifierMap = Map.add name name identifierMap
        let scopeSet = Set.add name scopeSet
        let linkageSet = Set.add name linkageSet
        
        let! resolvedParameters, (newIdentifierMap, newScopeSet) = resolveParameters (identifierMap, Set.empty) parameters []
        
        let! resolvedBody =
            body
            |> Option.map (fun x -> resolveBlock x (newIdentifierMap, newScopeSet, linkageSet))
            |> Option.sequenceResult
        
        return Function (name, resolvedParameters, resolvedBody), (identifierMap, scopeSet, linkageSet)
    }
    
let resolveProgram (Program functions) =
    let rec resolveFunctions state funcs acc =
        match funcs with
        | [] -> Ok acc
        | func :: rest ->
            let result = resolveFunctionDeclaration func state
            match result with
            | Error error -> Error error
            | Ok (resolvedFunc, state) -> resolveFunctions state rest (acc @ [resolvedFunc])
    
    resolveFunctions (Map.empty, Set.empty, Set.empty) functions []
    |> Result.map Program

// ------------------------------------------------- Type Checking ---------------------------------------------------

let rec typeCheckExpression symbolsMap expr =
    let typeCheckExpressionList arg =
            arg
            |> Seq.map (typeCheckExpression symbolsMap)
            |> Seq.sequenceResultM
            |> Result.map (Seq.iter (fun _ -> ()))
    
    match expr with
    | Var varName ->
        let varType = Map.find varName symbolsMap
        match varType with
        | Int -> Ok ()
        | _ -> Error <| Message $"Function '{varName}' used as variable"
    | FunctionCall (funcName, arguments) ->
        let funcType = Map.find funcName symbolsMap
        match funcType with
        | Int -> Error <| Message $"Variable '{funcName}' used as function"
        | FunType x when x = List.length arguments -> typeCheckExpressionList arguments
        | FunType _ -> Error <| Message $"Function '{funcName}' called with incorrect number of arguments"
    | Assignment(lvalue, rvalue) -> typeCheckExpressionList [lvalue; rvalue]
    | Unary(_, expression) -> typeCheckExpression symbolsMap expression
    | Binary(_, left, right) -> typeCheckExpressionList [left; right]
    | Conditional(condition, middle, right) -> typeCheckExpressionList [condition; middle; right]
    | Constant _ -> Ok ()

let typeCheckOptionalExpression symbolsMap optExpr =
    match optExpr with
    | None -> Ok ()
    | Some expr -> typeCheckExpression symbolsMap expr

let rec typeCheckVariableDeclaration symbolsMap (Variable (name, init)) =
    let symbolsMap = Map.add name Int symbolsMap
    match init with
    | None -> Ok symbolsMap
    | Some expr -> result {
        let! () = typeCheckExpression symbolsMap expr
        return symbolsMap
        }

and typeCheckFunctionDeclaration (symbolsMap, funcDefinedSet) (Function (name, parameters, body)) =
    let funcType = FunType <| List.length parameters
    
    let validateDeclaration =
        if Map.containsKey name symbolsMap then
            let oldType = Map.find name symbolsMap
            if oldType <> funcType then
                Error <| Message $"Incompatible function declaration for function '{name}'\nOld type: {oldType}\nnewType: {funcType}"
            else
            let alreadyDefined = Set.contains name funcDefinedSet
            if alreadyDefined && Option.isSome body then
                Error <| Message $"Multiple definitions for function '{name}'"
            else Ok ()
        else Ok ()
        
    result {
        let! () = validateDeclaration
        
        let symbolsMap = Map.add name funcType symbolsMap
        
        let registerParameter state parameter =
            Map.add parameter Int state
        let symbolsMap = List.fold registerParameter symbolsMap parameters
        let funcDefinedSet =
            match body with
            | None -> funcDefinedSet
            | Some _ -> Set.add name funcDefinedSet
            
        match body with
        | None -> return symbolsMap, funcDefinedSet
        | Some block ->
            let! state = typeCheckBlock (symbolsMap, funcDefinedSet) block
            return state
    }

and typeCheckForInit (symbolsMap, funcDefinedSet as state) init =
    match init with
    | InitExpression None -> Ok state
    | InitExpression (Some expr) -> result {
        let! () = typeCheckExpression symbolsMap expr
        return state
        }
    | InitDeclaration varDecl -> result {
        let! symbolsMap = typeCheckVariableDeclaration symbolsMap varDecl
        return symbolsMap, funcDefinedSet
        }

and typeCheckStatement (symbolsMap, _ as state) statement =
    match statement with
    | Return expr -> result {
        let! () = typeCheckExpression symbolsMap expr
        return state
        }
    | Expression expression -> result {
        let! () = typeCheckExpression symbolsMap expression
        return state
        }
    | If(condition, body, elseBody) -> result {
        let! () = typeCheckExpression symbolsMap condition
        let! state = typeCheckStatement state body
        match elseBody with
        | None -> return state
        | Some elseStatement ->
            let! state = typeCheckStatement state elseStatement
            return state
        }
    | Label(_, statement) -> typeCheckStatement state statement
    | Compound block -> typeCheckBlock state block
    | DummyWhile(condition, body) -> result {
        let! () = typeCheckExpression symbolsMap condition
        return! typeCheckStatement state body
        }
    | DummyDoWhile(body, condition) -> result {
        let! () = typeCheckExpression symbolsMap condition
        return! typeCheckStatement state body
        }
    | DummyFor(forInit, condition, post, body) -> result {
        let! symbolsMap, _ as state = typeCheckForInit state forInit
        let! () = typeCheckOptionalExpression symbolsMap condition
        let! () = typeCheckOptionalExpression symbolsMap post
        return! typeCheckStatement state body
        }
    | DummySwitch(argument, body) -> result {
        let! () = typeCheckExpression symbolsMap argument
        return! typeCheckStatement state body
        }
    | DummyCase(case, body) -> result {
        let! () = typeCheckExpression symbolsMap case
        return! typeCheckStatement state body
        }
    | DummyDefault body -> typeCheckStatement state body
    
    | Goto _
    | DummyBreak
    | DummyContinue
    | Null -> Ok state
    
    | LoopBreak _
    | Continue _
    | While _
    | DoWhile _
    | For _ -> failwith "Loop labeling has to be performed after type checking"
    
    | Switch _
    | Case _
    | Default _
    | SwitchBreak _ -> failwith "Switch labeling has to be performed after type checking"

and typeCheckBlockItem (symbolsMap, funcDefinedSet as state) item =
    match item with
    | Declaration (VariableDecl var) -> result {
        let! symbolsMap = typeCheckVariableDeclaration symbolsMap var
        return symbolsMap, funcDefinedSet
        }
    | Declaration (FunctionDecl func) -> typeCheckFunctionDeclaration state func
    | Statement statement -> typeCheckStatement state statement
    
and typeCheckBlock state block =
    let rec loop state items =
        match items with
        | [] -> Ok state
        | item :: rest ->
            let checkedItem = typeCheckBlockItem state item
            match checkedItem with
            | Error error -> Error error
            | Ok state -> loop state rest
    
    loop state block
    
let typeCheckProgram (Program functions) =
    let rec loop state functions =
        match functions with
        | [] -> Ok state
        | func :: rest ->
            let checkedFunction = typeCheckFunctionDeclaration state func
            match checkedFunction with
            | Error error -> Error error
            | Ok state -> loop state rest
            
    loop (Map.empty, Set.empty) functions

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

let resolveGotoFunction (Function(name, parameters, body)) =
    match body with
    | None -> Ok (Function (name, parameters, None))
    | Some block -> result {
        let emptyState = (Map.empty, Set.empty)
        let! resolvedBlock, _ = resolveGotoBlock block emptyState
        return Function (name, parameters, Some resolvedBlock)
        }

let rec resolveGotoProgram (Program functions) =
    functions
    |> Seq.map resolveGotoFunction
    |> Seq.sequenceResultM
    |> Result.map Array.toList
    |> Result.map Program

// ------------------------------------- Switch Labeling -----------------------------------------------------------

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

let resolveSwitchFunction (Function(name, parameters, body)) =
    match body with
    | None -> Ok (Function (name, parameters, None))
    | Some block -> result {
        let! resolvedBody, _ = resolveSwitchBlock block (None, false, Set.empty, List.empty)
        return Function (name, parameters, Some resolvedBody)
        }

let resolveSwitchProgram (Program functions) =
    functions
    |> Seq.map resolveSwitchFunction
    |> Seq.sequenceResultM
    |> Result.map Array.toList
    |> Result.map Program

// --------------------------------------- Loop Labeling -----------------------------------------------------------

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

let resolveLoopFunction (Function(name, parameters, body)) =
    match body with
    | None -> Ok (Function (name, parameters, None))
    | Some block -> result {
        let! resolvedBody = resolveLoopBlock block None
        return Function (name, parameters, Some resolvedBody)
        }

let resolveLoopProgram (Program functions) =
    functions
    |> Seq.map resolveLoopFunction
    |> Seq.sequenceResultM
    |> Result.map Array.toList
    |> Result.map Program

// ------------------------------- Complete Semantic Analysis ------------------------------------------------------

let semanticAnalysis program=
    result {
        let! program = resolveProgram program
        let! state = typeCheckProgram program
        return program 
        }
    |> Result.bind resolveGotoProgram
    |> Result.bind resolveSwitchProgram
    |> Result.bind resolveLoopProgram
    