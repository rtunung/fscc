open System
open System.IO
open System.Linq
open System.Diagnostics
open FsToolkit.ErrorHandling
open fscc

let args = Environment.GetCommandLineArgs ()
 
let onlyParse = args.Contains "--parse"
let onlyLex = args.Contains "--lex"
let onlyCodeGen = args.Contains "--codegen"
let onlyTacky = args.Contains "--tacky"
let onlyAssembly = args.Contains "--assembly"
let onlyValidate = args.Contains "--validate"

let compileObjectFile = args.Contains "-c"

let filterArgs = ["--parse"; "--lex"; "--codegen"; "--tacky"; "--assembly"; "--validate"; "-c"]
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
    exit 1
    
let tokenResult = getTokens inputFile[0] 
 
let printResult a =
    match a with
    | Error error ->
        eprintfn "An error occured\n%A" error
        exit 1
    | Ok result -> printfn "%A" result
    
if onlyLex then
    printResult tokenResult
    exit 0
    
let parseResult =
    tokenResult
    |> Result.mapError C.LexError
    |> Result.bind C.parseProgram
    
if onlyParse then
    printResult parseResult
    exit 0
    
let validatedResult =
    parseResult
    |> Result.bind SemanticAnalysis.semanticAnalysis
    
if onlyValidate then
    printResult validatedResult
    exit 0
    
let tackyResult = result {
    let! cProgram, symbolTable = validatedResult
    return Tacky.fromProgram symbolTable cProgram
    }
    
if onlyTacky then
    printResult tackyResult
    exit 0

let assemblyResult = result {
    let! _, symbolTable = validatedResult
    let! tacky = tackyResult
    let code =
        tacky
        |> Assembly.fromProgram
        |> Assembly.updateProgram symbolTable
    return code
    }
    
if onlyCodeGen then
    printResult assemblyResult
    exit 0
    
let assembly =
    assemblyResult
    |> Result.map Assembly.emitProgram
    

if onlyAssembly then
    match assembly with
    | Error error ->
        eprintfn "An error occured:\n%A" error
        exit 1
    | Ok output ->
        printfn "%s" output
        exit 0
    
match assembly with
| Error error ->
    eprintf "An error occured:\n%A" error
    exit 1
| _ -> ()
    
let assemblyString = Result.defaultValue "" assembly
    
let outputFile =
    let extensionBegin = inputFile[0].LastIndexOf '.'
    let root = inputFile[0].Substring(0, extensionBegin)
    if compileObjectFile then
        root + ".o"
    else
        root
    
let outputAssembly = outputFile + ".s"

File.WriteAllText (outputAssembly, assemblyString)
let proc =
        if compileObjectFile then
            Process.Start ("gcc", $"-c {outputAssembly} -g -o {outputFile}")
        else
            Process.Start ("gcc", $"{outputAssembly} -g -o {outputFile}")
        
proc.WaitForExit ()
let gccExitCode = proc.ExitCode

File.Delete outputAssembly
if gccExitCode <> 0 then
    exit 1