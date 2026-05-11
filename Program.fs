// For more information see https://aka.ms/fsharp-console-apps

open System
open System.IO
open fscc

let args = Environment.GetCommandLineArgs ()

let printAST filename =
    File.ReadAllText filename
    |> Lexer.fromString
    |> Lexer.runLexer
    |> Result.defaultValue [Lexer.EOF]
    |> Parser.parseProgram
    |> printfn "%A"

if args.Length >= 2 then printAST args[1]
else printfn "No input file!"