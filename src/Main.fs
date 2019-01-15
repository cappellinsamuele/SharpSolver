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
open System.Security.Cryptography


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

            //functionOutputEqu: funzione che viene chiamata nel pattern Match di Equ. Questo serve per eliminare la ripetizione del codice in ogni caso del pattern match dove alla fine bisogna stampare a video i risultati ottenuti
            let functionOutputEqu (monomialList : monomial list) =  let normalizedList = Impl.normalize(Polynomial(monomialList))
                                                                    norm "%O = 0" normalizedList

                                                                    let equDegree = Impl.polynomial_degree(Polynomial(monomialList))
                                                                    hout "degree" "%O" equDegree

                                                                    if Impl.polynomial_degree(Polynomial(monomialList)) = 0 then
                                                                        if Impl.solve0(normalizedList) then ident "%O" "True"
                                                                                                       else ident "%O" "False"

                                                                    else if Impl.polynomial_degree(Polynomial(monomialList)) = 1 then
                                                                     let resultGradeOne = Impl.solve1(normalizedList)
                                                                     sol "x = %O" resultGradeOne

                                                                    else if Impl.polynomial_degree(Polynomial(monomialList)) = 2 then   
                                                                      let resultGradeTwo = Impl.solve2(normalizedList)
                                                                      //Scompatto il valore di resultGradeTwo così da ottenere i valori x1,x2 dell'equazione di secondo grado
                                                                      let mutable x1 = 0.
                                                                      let mutable x2 : float option = None
                                                                      match resultGradeTwo with
                                                                      |Some (a, b) -> x1 <- a
                                                                                      x2 <- b
                                                                      |None -> x1<-0.
                                                                      sol "x1 = %O vel x2 = %O" x1 x2.Value
    
            //functionOutputExpr svolge la stessa funzione di functionOutputEqu solo che questo viene invocato all'interno del match di Expr.
            let functionOutputExpr (toDer : expr) = let reduxExpr = Impl.reduce(toDer)
                                                    redux "%O" reduxExpr
                                                    let normalizedExpr = Impl.normalize reduxExpr
                                                    norm "%O" normalizedExpr
                                                    let polynomialDegree = Impl.normalized_polynomial_degree(normalizedExpr)
                                                    hout "degree" "%O" polynomialDegree

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

            (*Gestione del pattern match per i Casi Expr ed Equ:
                - Expr: ricevo in input un valore di tipo Expr, il quale può contenere Poly oppure Derive. Nel secondo caso, applico il reduce all'espressione, in modo tale da derivarla. Prendo poi il polinomio ottenuto e applico functionOutputExpr per generare l'output.
                - Equ: ricevo in input due valori di tipo Expr, che possono essere Poly o Derive. In base al loro tipo svolgo il reduce dell'espressione di tipo Derive, concateno i le due liste di monomi e infine applico functionOutputEqu per generare l'output.
            *)
            |Expr e1 -> 
                match e1 with
                    Poly toDer -> functionOutputExpr e1                                  
                    |Derive toDer -> functionOutputExpr e1

            |Equ (e1, e2) ->                 
                match e1, e2 with
                ((Poly a), (Poly b)) -> 
                                        redux "%O = %O" a b
                                        match a,Impl.polynomial_negate (b) with
                                        Polynomial a1, Polynomial b1 -> 
                                            let monomialList = a1 @ b1                                            
                                            functionOutputEqu monomialList
                                                 
                |(Derive a),(Derive b) -> let reduceA = Impl.reduce(e1)
                                          let reduceB = Impl.reduce(e2)
                                          redux "%O = %O" reduceA reduceB 
                                          match reduceA,Impl.polynomial_negate(reduceB) with
                                          Polynomial a1,Polynomial b1 ->
                                            let monomialList = a1 @ b1
                                            functionOutputEqu monomialList

                |(Poly a),(Derive b) -> let reduceB = Impl.reduce(e2)
                                        redux "%O = %O" a reduceB
                                        match a,Impl.polynomial_negate(reduceB) with
                                        Polynomial a1,Polynomial b1 ->
                                          let monomialList = a1 @ b1
                                          functionOutputEqu monomialList
                
                |(Derive a),(Poly b) -> let reduceA = Impl.reduce(e1)
                                        redux "%O = %O" reduceA b
                                        match reduceA,Impl.polynomial_negate(b) with
                                        Polynomial a1,Polynomial b1 ->
                                          let monomialList = a1 @ b1
                                          functionOutputEqu monomialList
              
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


