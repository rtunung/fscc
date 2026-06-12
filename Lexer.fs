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
    | IfKey
    | ElseKey
    | GotoKey
    | DoKey
    | WhileKey
    | ForKey
    | BreakKey
    | ContinueKey
    | SwitchKey
    | CaseKey
    | DefaultKey
    | StaticKey
    | ExternKey
    
    | ParenOpen
    | ParenClose
    | BraceOpen
    | BraceClose
    | Semicolon
    | Comma
    | Tilde
    | Minus
    | Decrement
    | Plus
    | Increment
    | Asterisk
    | Slash
    | Percentage
    | Pipe
    | Ampersand
    | Caret
    | ShiftLeft
    | ShiftRight
    | Greater
    | Less
    | DoublePipe
    | DoubleAmpersand
    | DoubleEqual
    | Equal
    | Exclamation
    | ExclamationEqual
    | GreaterEqual
    | LessEqual
    | QuestionMark
    | Colon
    | PlusEqual
    | MinusEqual
    | StarEqual
    | SlashEqual
    | PercentageEqual
    | AmpersandEqual
    | PipeEqual
    | CaretEqual
    | ShiftLeftEqual
    | ShiftRightEqual
    
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

let rec skipUntilNewline lexer =
    match peek lexer with
    | Some '\n' -> advance lexer
    | Some _ -> skipUntilNewline (advance lexer)
    | None -> lexer

let rec skipUntilCommentBlockEnd lexer =
    let advLexer = advance lexer
    match peek lexer, peek advLexer with
    | Some '*', Some '/' -> advance advLexer
    | None, _ -> lexer
    | _, _ -> skipUntilCommentBlockEnd advLexer

let rec skipWhiteSpaceAndComments lexer =
    match peek lexer with
     // Skipping preprocessor directives for now! TODO: Change this once we actual have a preprocessor!!!
    | Some '#' -> skipWhiteSpaceAndComments (skipUntilNewline lexer) 
    | Some chr when Char.IsWhiteSpace(chr) -> skipWhiteSpaceAndComments (advance lexer)
    | Some '/' ->
        match peek (advance lexer) with
        | Some '/' -> // Line Comment
            skipWhiteSpaceAndComments (skipUntilNewline lexer)
        | Some '*' -> // Block Comment
            skipWhiteSpaceAndComments (skipUntilCommentBlockEnd lexer)
        | _ -> lexer
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
        | Some chr when Char.IsLetterOrDigit(chr) || chr = '_' -> loop (advance lex) (acc + string chr)
        | _ -> acc, lex
    let ident, nextLex = loop lexer ""
    let token =
        match ident with
        | "int" -> IntKey
        | "void" -> VoidKey
        | "return" -> ReturnKey
        | "if" -> IfKey
        | "else" -> ElseKey
        | "goto" -> GotoKey
        | "do" -> DoKey
        | "while" -> WhileKey
        | "for" -> ForKey
        | "break" -> BreakKey
        | "continue" ->  ContinueKey
        | "switch" -> SwitchKey
        | "case" -> CaseKey
        | "default" -> DefaultKey
        | "static" -> StaticKey
        | "extern" -> ExternKey
        | value -> Identifier value
    token, nextLex

let nextToken lexer =
    let advLexer = advance lexer
    match peek lexer with
    | None -> Ok (EOF, lexer)
    | Some ';' -> Ok ( Semicolon, advLexer )
    | Some '(' -> Ok ( ParenOpen, advLexer )
    | Some ')' -> Ok ( ParenClose, advLexer )
    | Some '{' -> Ok ( BraceOpen, advLexer )
    | Some '}' -> Ok ( BraceClose, advLexer )
    | Some '~' -> Ok ( Tilde, advLexer )
    | Some ',' -> Ok (Comma, advLexer)
    | Some '*' ->
        match peek advLexer with
        | Some '=' -> Ok(StarEqual, advance advLexer)
        | _ -> Ok ( Asterisk, advLexer )
    | Some '/' ->
        match peek advLexer with
        | Some '=' -> Ok (SlashEqual, advance advLexer)
        | _ -> Ok ( Slash, advLexer )
    | Some '%' ->
        match peek advLexer with
        | Some '=' -> Ok (PercentageEqual, advance advLexer)
        | _ -> Ok ( Percentage, advLexer )
    | Some '?' -> Ok ( QuestionMark, advLexer)
    | Some ':' -> Ok ( Colon, advLexer )
    | Some '|' ->
        match peek advLexer with
        | Some '|' -> Ok (DoublePipe, advance advLexer)
        | Some '=' -> Ok (PipeEqual, advance advLexer)
        | _ -> Ok ( Pipe, advLexer )
    | Some '&' ->
        match peek advLexer with
        | Some '&' -> Ok (DoubleAmpersand, advance advLexer)
        | Some '=' -> Ok (AmpersandEqual, advance advLexer)
        | _ -> Ok ( Ampersand, advLexer )
    | Some '^' ->
        match peek advLexer with
        | Some '=' -> Ok (CaretEqual, advance advLexer)
        | _ -> Ok ( Caret, advLexer )
    | Some '!' ->
        match peek advLexer with
        | Some '=' -> Ok (ExclamationEqual, advance advLexer)
        | _ -> Ok (Exclamation, advLexer)
    | Some '>' ->
        let dAdvLexer = advance advLexer
        match peek advLexer, peek dAdvLexer with
        | Some '>', Some '=' -> Ok (ShiftRightEqual, advance dAdvLexer)
        | Some '>', _ -> Ok (ShiftRight, dAdvLexer)
        | Some '=', _ -> Ok (GreaterEqual, dAdvLexer)
        | _ -> Ok (Greater, advLexer)
    | Some '<' ->
        let dAdvLexer = advance advLexer
        match peek advLexer, peek dAdvLexer with
        | Some '<', Some '=' -> Ok (ShiftLeftEqual, advance dAdvLexer)
        | Some '<', _ -> Ok (ShiftLeft, dAdvLexer)
        | Some '=', _ -> Ok (LessEqual, dAdvLexer)
        | _ -> Ok (Less, advLexer)
    | Some '=' ->
        match peek advLexer with
        | Some '=' -> Ok (DoubleEqual, advance advLexer)
        | _ -> Ok (Equal, advLexer)
    | Some '-' ->
        match peek advLexer with
        | Some '-' -> Ok ( Decrement, advance advLexer)
        | Some '=' -> Ok ( MinusEqual, advance advLexer)
        | _ -> Ok ( Minus, advLexer )
    | Some '+' ->
        match peek advLexer with
        | Some '+' -> Ok ( Increment, advance advLexer)
        | Some '=' -> Ok ( PlusEqual, advance advLexer)
        | _ -> Ok ( Plus, advLexer )
    | Some chr when Char.IsDigit(chr) ->  lexConstant lexer
    | Some chr when Char.IsLetter(chr) || chr = '_' -> Ok <| lexIdentifierKeyword lexer
    | Some unknownChar -> Error <| makeLexerError lexer $"Unexpected character '{unknownChar}'"

let runLexer lexer =
    let rec loop lex acc =
        let result = lex |> skipWhiteSpaceAndComments |> nextToken
        match result with
        | Error lexerError -> Error lexerError
        | Ok ( EOF, _) ->  Ok acc
        | Ok (token, nextLex) -> loop nextLex (acc @ [token])
    loop lexer []
