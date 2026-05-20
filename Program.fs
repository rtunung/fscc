open System
open System.IO
open System.Linq
open System.Diagnostics
open fscc

let args = Environment.GetCommandLineArgs ()
 
let onlyParse = args.Contains "--parse"
let onlyLex = args.Contains "--lex"
let onlyCodeGen = args.Contains "--codegen"
let onlyTacky = args.Contains "--tacky"
let onlyAssembly = args.Contains "--assembly"

let filterArgs = ["--parse"; "--lex"; "--codegen"; "--tacky"; "--assembly"]
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
    | Error error ->
        eprintfn "An error occured\n%A" error
        Environment.Exit 1
    | Ok result -> printfn "%A" result
    
if onlyLex then
    printResult tokenResult
    Environment.Exit 0
    
let parseResult =
    tokenResult
    |> Result.mapError C.LexError
    |> Result.bind C.parseProgram
    
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

if onlyCodeGen then
    printResult assemblyResult
    Environment.Exit 0
    
let assembly =
    assemblyResult
    |> Result.map Assembly.emitProgram
    

if onlyAssembly then
    match assembly with
    | Error error ->
        eprintfn "An error occured:\n%A" error
        Environment.Exit 1
    | Ok output ->
        printfn "%s" output
        Environment.Exit 0
    
match assembly with
| Error error ->
    eprintf "An error occured:\n%A" error
    Environment.Exit 1
| _ -> ()
    
let assemblyString = Result.defaultValue "" assembly
    
let outputFile =
    let extensionBegin = inputFile[0].LastIndexOf '.'
    inputFile[0].Substring(0, extensionBegin)
    
let outputAssembly = outputFile + ".s"

File.WriteAllText (outputAssembly, assemblyString)
let proc = Process.Start ("gcc", $"{outputAssembly} -o {outputFile}")
proc.WaitForExit ()
let gccExitCode = proc.ExitCode

File.Delete outputAssembly
if gccExitCode <> 0 then
    Environment.Exit 1