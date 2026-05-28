module fscc.Misc

// Name generators
// Global mutable state, very evil
let mutable tempVariableCounter = 0
let getTemporaryName () =
    let name = $"temp.{tempVariableCounter}"
    tempVariableCounter <- tempVariableCounter + 1
    name
    
let mutable falseLabelCounter = 0
let getFalseLabel () =
    let label = $"false.{falseLabelCounter}"
    falseLabelCounter <- falseLabelCounter + 1
    label
    
let mutable endLabelCounter = 0
let getEndLabel () =
    let label = $"end.{endLabelCounter}"
    endLabelCounter <- endLabelCounter + 1
    label
    
let mutable elseLabelCounter = 0
let getElseLabel () =
    let label = $"else.{elseLabelCounter}"
    elseLabelCounter <- elseLabelCounter + 1
    label
    
let mutable gotoLabelCounter = 0
let getGotoLabel () =
    let label = $"goto.{gotoLabelCounter}"
    gotoLabelCounter <- gotoLabelCounter + 1
    label
    
let mutable loopLabelcounter = 0
let getLoopLabel () =
    let label = $"loop.{loopLabelcounter}"
    loopLabelcounter <- loopLabelcounter + 1
    label