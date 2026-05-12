module fscc.Lexer

open System

type Lexer = {
    Data : string
    Position : int
}

type Token =
    | Identifier of string
    | Constant of int
    | IntKey
    | VoidKey
    | ReturnKey
    | ParenOpen
    | ParenClose
    | BraceOpen
    | BraceClose
    | Semicolon
    | Tilde
    | Minus
    | Decrement
    | EOF

type LexerError = {
    Message : string
    Position : int * int 
}

let fromString str = { Data = str; Position = 0}

let advance lexer : Lexer = { lexer with Position = lexer.Position + 1}

let getPosition lexer =
    let trackPosition (line, column) chr =
        if chr = '\n' then (line + 1, 1)
        else (line, column + 1)
    lexer.Data
    |> Seq.take lexer.Position
    |> Seq.fold trackPosition (1,1)


let makeLexerError lexer message = { Message = message; Position = getPosition lexer}

let peek (lexer:Lexer) =
    if lexer.Position < lexer.Data.Length then Some lexer.Data[lexer.Position]
    else None

let rec skipWhiteSpace lexer =
    match peek lexer with
    | None -> lexer
    | Some chr when Char.IsWhiteSpace(chr) -> skipWhiteSpace (advance lexer)
    | _ -> lexer

let lexConstant lexer =
    let rec loop lex acc = 
        match peek lex with
        | Some chr when Char.IsDigit(chr) -> loop (advance lex) (acc  + string chr)
        | Some chr when Char.IsLetter(chr) -> Error <| makeLexerError lex $"Unexpected '{chr}' at end of constant '{acc}'"
        | _ -> Ok (Constant <| Int32.Parse acc, lex)
    loop lexer ""
    
let lexIdentifierKeyword lexer =
    let rec loop lex acc =
        match peek lex with
        | Some chr when Char.IsLetterOrDigit(chr) -> loop (advance lex) (acc + string chr)
        | _ -> acc, lex
    let ident, nextLex = loop lexer ""
    let token =
        match ident with
        | "int" -> IntKey
        | "void" -> VoidKey
        | "return" -> ReturnKey
        | value -> Identifier value
    token, nextLex

let nextToken lexer =
    match peek lexer with
    | None -> Ok (EOF, lexer)
    | Some ';' -> Ok ( Semicolon, advance lexer )
    | Some '(' -> Ok ( ParenOpen, advance lexer )
    | Some ')' -> Ok ( ParenClose, advance lexer )
    | Some '{' -> Ok ( BraceOpen, advance lexer )
    | Some '}' -> Ok ( BraceClose, advance lexer )
    | Some '~' -> Ok ( Tilde, advance lexer )
    | Some '-' ->
        let advLexer = advance lexer
        match peek advLexer with
        | Some '-' -> Ok ( Decrement, advance advLexer)
        | _ -> Ok ( Minus, advLexer )
    | Some chr when Char.IsDigit(chr) ->  lexConstant lexer
    | Some chr when Char.IsLetter(chr) -> Ok <| lexIdentifierKeyword lexer
    | Some unknownChar -> Error <| makeLexerError lexer $"Unexpected character '{unknownChar}'"

let runLexer lexer =
    let rec loop lex acc =
        let result = lex |> skipWhiteSpace |> nextToken
        match result with
        | Error lexerError -> Error lexerError
        | Ok ( EOF, _) ->  Ok acc
        | Ok (token, nextLex) -> loop nextLex (acc @ [token])
    loop lexer []

