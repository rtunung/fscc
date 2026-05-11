open System
open System.IO
open fscc

let args = Environment.GetCommandLineArgs ()

let getAssembly filename =
    File.ReadAllText filename
    |> Lexer.fromString
    |> Lexer.runLexer
    |> Result.defaultValue [Lexer.EOF]
    |> Parser.parseProgram
    |> Result.map Assembly.toAssemblyProgram
    |> Result.map Assembly.emitProgram

if args.Length >= 2 then
    match getAssembly args[1] with
    | Error value -> eprintfn $"Error %A{value}"
    | Ok assembly -> printfn $"%s{assembly}"
else eprintfn "No input file!"