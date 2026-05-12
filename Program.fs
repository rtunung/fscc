open System
open System.IO
open System.Linq
open fscc

let args = Environment.GetCommandLineArgs ()
 
let onlyParse = args.Contains "--parse"
let onlyLex = args.Contains "--lex"
let onlyAssemblyAst = args.Contains "--codegen"
let onlyTacky = args.Contains "--tacky"

let filterArgs = ["--parse"; "--lex"; "--codegen"; "--tacky"]
let inputFile =
    args
    |> Seq.skip 1
    |> Seq.filter (fun x -> not <| List.contains x filterArgs)
    |> Seq.toArray

let getTokens filename =
    File.ReadAllText filename
    |> Lexer.fromString
    |> Lexer.runLexer

if inputFile.Length <= 0 then
    eprintfn "No input file!"
    Environment.Exit -1
    
let tokenResult = getTokens inputFile[0] 
 
let printResult a =
    match a with
    | Error error -> eprintfn "An error occured\n%A" error
    | Ok result -> printfn "%A" result
    
if onlyLex then
    printResult tokenResult
    Environment.Exit 0
    
let parseResult =
    tokenResult
    |> Result.mapError CAst.LexError
    |> Result.bind CAst.parseProgram
    
if onlyParse then
    printResult parseResult
    Environment.Exit 0
    
let tackyResult =
    parseResult
    |> Result.map Tacky.fromProgram
    
if onlyTacky then
    printResult tackyResult
    Environment.Exit 0

let assemblyResult =
    tackyResult
    |> Result.map Assembly.fromProgram
    |> Result.map Assembly.updateAllInstructions

if onlyAssemblyAst then
    printResult assemblyResult
    Environment.Exit 0
    
let finalAssembly =
    assemblyResult
    |> Result.map Assembly.emitProgram
    
match finalAssembly with
| Error error -> eprintfn "An error occured:\n%A" error
| Ok output -> printfn "%s" output