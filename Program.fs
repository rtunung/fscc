open System
open System.IO
open System.Linq
open fscc

let args = Environment.GetCommandLineArgs ()
 
let onlyParse = args.Contains "--parse"
let onlyLex = args.Contains "--lex"
let onlyAssemblyAst = args.Contains "--codegen"

let filterArgs = ["--parse"; "--lex"; "--codegen"]
let inputFile =
    args
    |> Seq.skip 1
    |> Seq.filter (fun x -> not <| List.contains x filterArgs)
    |> Seq.toArray

let getTokens filename =
    File.ReadAllText filename
    |> Lexer.fromString
    |> Lexer.runLexer
    
    // |> Result.defaultValue [Lexer.EOF]
    // |> Parser.parseProgram
    // |> Result.map Assembly.toAssemblyProgram
    // |> Result.map Assembly.emitProgram

if inputFile.Length < 0 then
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
    |> Result.mapError Parser.LexError
    |> Result.bind Parser.parseProgram
    
if onlyParse then
    printResult parseResult
    Environment.Exit 0
    
let codegenResult =
    parseResult
    |> Result.map Assembly.toAssemblyProgram
    
if onlyAssemblyAst then
    printResult codegenResult
    Environment.Exit 0
    
let assembly =
    codegenResult
    |> Result.map Assembly.emitProgram
    
match assembly with
| Error error -> eprintfn "An error occured:\n%A" error
| Ok output -> printfn "%s" output