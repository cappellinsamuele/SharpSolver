(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Main.fs: console e codice main
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Main

open Microsoft.FSharp.Text.Lexing
open Absyn
open System
open Prelude
open Impl
open Microsoft.FSharp.Text
open SharpSolver
open SharpSolver
open SharpSolver
open SharpSolver
open SharpSolver
open SharpSolver
open SharpSolver


// funzioni di logging e printing
//

let hout hd fmt =
    if not <| String.IsNullOrWhiteSpace hd then
        printf "[%s]%s" hd (new String (' ', max 1 (Config.prefix_max_len - String.length hd)))
        stdout.Flush ()
    printfn fmt

let chout col hd fmt =
    let c = Console.ForegroundColor
    Console.ForegroundColor <- col
    Printf.kprintf (fun s -> hout hd "%s" s; Console.ForegroundColor <- c) fmt

let out fmt = hout "" fmt
let cout col fmt = chout col "" fmt

let norm fmt = chout ConsoleColor.Yellow "norm" fmt
let redux fmt = chout ConsoleColor.Magenta "redux" fmt
let sol fmt = chout ConsoleColor.Green "sol" fmt
let ident fmt = chout ConsoleColor.Green "ident" fmt    
let error fmt = chout ConsoleColor.Red "error" fmt   

// interprete dei comandi e delle espressioni
//

let interpreter_loop () =
    while true do
        printf "\n%s" Config.prompt_prefix          // stampa il prompt
        stdout.Flush ()                             // per sicurezza flusha lo stdout per vedere la stampa del prompt senza end-of-line
        let input = Console.ReadLine ()             // leggi l'input scritto dall'utente
        let lexbuf = LexBuffer<_>.FromString input  // crea un lexbuffer sulla stringa di input

        // funzione locale per il pretty-printing degli errori
        let localized_error msg =
            let tabs = new string (' ', Config.prompt_prefix.Length + lexbuf.StartPos.Column)
            let cuts = new string ('^', let n = lexbuf.EndPos.Column - lexbuf.StartPos.Column in if n > 0 then n else 1)
            cout ConsoleColor.Yellow "%s%s\n" tabs cuts
            error "error at %d-%d: %s" lexbuf.StartPos.Column lexbuf.EndPos.Column msg 
        
        // blocco con trapping delle eccezioni
        try
            let line = Parser.line Lexer.tokenize lexbuf    // invoca il parser sul lexbuffer usando il lexer come tokenizzatore
            #if DEBUG
            hout "absyn" "%+A" line
            hout "pretty" "%O" line
            #endif

            // interpreta la linea in base al valore di tipo line prodotto dal parsing
            match line with
            | Cmd "help" ->
                out "%s" Config.help_text

            | Cmd ("quit" | "exit") ->
                out "%s" Config.exit_text
                exit 0

            // TODO: se volete supportare altri comandi, fatelo qui (opzionale)
            
            | Cmd s -> error "unknown command: %s" s    // i comandi non conosciuti cadono in questo caso

            // TODO: aggiungere qui sotto i pattern per i casi Expr ed Equ con relativo codice per, rispettivamente, normalizzare espressioni e risolvere equazioni

            |Expr e1 -> 
                match e1 with
                    Poly toDer -> hout "redux" "%O" (Impl.reduce(e1))
                                  //let polynomailToDer = Impl.derive toDer
                                  //hout "derive" "%O" polynomailToDer
                                  let normalizedExpr = Impl.normalize toDer
                                  hout "norm" "%O" normalizedExpr
                                  let polynomialDegree = Impl.normalized_polynomial_degree(normalizedExpr)
                                  hout "degree" "%O" polynomialDegree
                                  
                    |Derive toDer -> hout "redux" "%O" (Impl.reduce(e1))
            |Equ (e1, e2) -> 
                match e1, e2 with           //Controllo i casi, guardo se Equ ha entrambi Poly di grado zero così da poter risolvere con solve0
                ((Poly a), (Poly b)) -> if Impl.polynomial_degree (a) = 0 && Impl.polynomial_degree (b) = 0 then
                                                let normPolynomialA = Impl.normalize(a)
                                                let normPolynomialB = Impl.normalize(b)
                                                if Impl.solve0(normPolynomialB) then hout "ident" "%O" (Impl.solve0 (normPolynomialA)) 
                                                else if normPolynomialA = normPolynomialB then hout "ident" "%O" "True"
                                                                                          else hout "ident" "%O" "False"
                                        
                                        else if  Impl.polynomial_degree (a) = 1 || Impl.polynomial_degree (b) = 1 then
                                                let normPolynomialA1 = Impl.normalize(a)
                                                let normPolynomialB1 = Impl.normalize(Impl.polynomial_negate(b))

                                                match normPolynomialA1,normPolynomialB1 with
                                                NormalizedPolynomial a1, NormalizedPolynomial b1 -> let mutable arrA = []
                                                                                                    let mutable arrB = []
                                                                                                    for i in a1 do
                                                                                                        arrA <- [i]@arrA
                                                                                                    for i in b1 do 
                                                                                                        arrB <- [i]@arrB

                                        else failwith "ERRORE"

                                            //Controllo se almeno uno dei due Poly ha grado uno e risolvo con solve1
                                            (*else if Impl.polynomial_degree (a) = 1 || Impl.polynomial_degree (b) = 1 then
                                                let valA1 = (Impl.normalize(a) :: Impl.normalize(b))
                                                let res = Impl.solve1(Impl.normalize(valA1))
                                                hout "solve1" res*)                                                 
                                            //if(Impl.solve0(Impl.normalize () )) then printf "[sol] 0" else printf "false"  //SMONTARE L'OGGETTO POLINOMIO E OTTENERE LA LISTA DI MONOMI VERA E PROPRIA
              
            | _ -> raise (NotImplementedException (sprintf "unknown command or expression: %O" line))
                   
        // gestione delle eccezioni
        with LexYacc.ParseErrorContextException ctx ->
                let ctx = ctx :?> Parsing.ParseErrorContext<Parser.token>
                localized_error (sprintf "syntax error%s" (match ctx.CurrentToken with Some t -> sprintf " at token <%O>" t | None -> ""))

           | Lexer.LexerError msg -> localized_error msg 

           | :? NotImplementedException as e -> error "%O" e
        
           | e -> localized_error e.Message


// funzione main: il programma comincia da qui
//

[<EntryPoint>]
let main _ = 
    let code =
        try
            interpreter_loop ()                 // chiama l'interprete
            0                                   // ritorna il codice di errore 0 (nessun errore) al sistema operativo se tutto è andato liscio
        with e -> error "fatal error: %O" e; 1  // in caso di eccezione esce con codice di errore 1
    #if DEBUG
    Console.ReadKey () |> ignore                // aspetta la pressione di un tasto prima di chiudere la finestra del terminare 
    #endif
    code


