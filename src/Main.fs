(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Main.fs: console e codice main
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

 (*
 PROGETTO DI:
 CAPPELLIN SAMUELE 876365
 MAROSTICA RICCARDO 874154
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

            let validPositions (arr:rational[]) : int = //Metodo che serve a normalizeArray per contare quante sono le posizioni con coefficienti non nulli
                let mutable pos = 0
                for i in arr do
                    if (i<>rational.Zero) then pos<-pos+1
                pos
            let normPrint (np:normalized_polynomial) = //Metodo che serve per la stampa del polinomio normalizzato. rimuove gli zeri dall'output. Zeri che tuttavia sono necessari per il corretto fuznionamento degli altri metodi
                 match np with
                 NormalizedPolynomial arr -> let res = Array.create (validPositions arr) (rational.Zero)
                                             let mutable pos = 0
                                             for r in arr do
                                                if (r<>rational.Zero) 
                                                    then res.[pos] <- r
                                                         pos <- pos + 1
                                             NormalizedPolynomial(res)

            //functionOutputEqu: metodo che viene chiamato nel pattern Match di Equ. Viene utilizzato questo metodo in modo tale da evitare la ripetizione del codice degli output in ogni caso del pattern match di Equ
            let functionOutputEqu (monomialList : monomial list) =  let normalizedList = Impl.normalize(Polynomial(monomialList))
                                                                    norm "%O = 0" normalizedList

                                                                    let equDegree = Impl.polynomial_degree(Polynomial(monomialList))
                                                                    hout "degree" "%O" equDegree

                                                                    //In base al grado del polinomio, verrà eseguito uno dei tre metodi per la risoluzione dell'equazione, ossia solve0, solve1 oppure solve2
                                                                    if Impl.polynomial_degree(Polynomial(monomialList)) = 0 then
                                                                        if Impl.solve0(normalizedList) then ident "%O" "true"
                                                                                                       else ident "%O" "false"

                                                                    else if Impl.polynomial_degree(Polynomial(monomialList)) = 1 then
                                                                     let resultGradeOne = Impl.solve1(normalizedList)
                                                                     sol "x = %O" resultGradeOne

                                                                    else if Impl.polynomial_degree(Polynomial(monomialList)) = 2 then   
                                                                      let resultGradeTwo = Impl.solve2(normalizedList)
                                                                      //Scompatto il valore di resultGradeTwo così da ottenere i valori x1,x2 dell'equazione di secondo grado
                                                                      let mutable x1 = 0.
                                                                      let mutable x2 : float option = None
                                                                      match resultGradeTwo with
                                                                      |Some (a, Some b) -> x1 <- a
                                                                                           x2 <- Some b
                                                                                           sol "x1 = %O vel x2 = %O" x1 x2.Value
                                                                      |Some (a, None) -> x1 <- a
                                                                                         x2 <- None
                                                                                         sol "x = %O" x1 
                                                                      |None -> sol "%O" None
    
            //functionOutputExpr: metodo che svolge la stessa funzione di functionOutputEqu però questo viene invocato all'interno del pattern match di Expr
            let functionOutputExpr (toDer : expr) = let reduxExpr = Impl.reduce(toDer)
                                                    redux "%O" reduxExpr
                                                    let normalizedExpr = Impl.normalize reduxExpr
                                                    let nPrint = normPrint normalizedExpr
                                                    norm "%O" nPrint
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

            |Expr e1 -> functionOutputExpr e1   //Quando ricevo in input un espressione, questa verrà passata al metodo functionOutputExpr il quale svolgerà, richiamando i metodi di Impl.fs, i metodo scritti al suo interno e infine stamperà a video gli output

            |Equ (e1, e2) ->                 
                match e1, e2 with           
                ((Poly a), (Poly b)) -> 
                                        redux "%O = %O" a b
                                        match a,Impl.polynomial_negate (b) with         //Sappiamo che il tipo polynomial è uguale a Polynomial of monomial list
                                        Polynomial a1, Polynomial b1 ->                 //Utilizzando il match vado ad ottenere le due monomial list dei polinomi a e b
                                            let monomialList = a1 @ b1                  //Concateno la monimial list a1 e b1 in modo tale da formare una lista contenente entrambi gli elementi                         
                                            functionOutputEqu monomialList              //Questa lista viene poi passata al metodo functionOutputEqu che stamperà gli output
                                                 
                |(Derive a),(Derive b) -> let reduceA = Impl.reduce(e1)                 //Essendo a e b di tipo expr, bisogna cambiare il loro tipo in polynomial. 
                                          let reduceB = Impl.reduce(e2)                 //Questo avviene attraverso il metodo Impl.reduce il quale svolge la derivata delle due espressioni fino a renderle di tipo polynomial
                                          redux "%O = %O" reduceA reduceB 
                                          match reduceA,Impl.polynomial_negate(reduceB) with    //Anche in questo caso concateno le due monomial list che poi verranno usate nel metodo functionOutputEqu
                                          Polynomial a1,Polynomial b1 ->
                                            let monomialList = a1 @ b1
                                            functionOutputEqu monomialList
                
                //In questi ultimi due casi del pattern match, solo una delle due espressioni deve essere derivata. Quindi verrà utilizzato il metodo Impl.reduce sulla valore di tipo expr mentre l'altro valore, di tipo polynomial non verrà toccato.
                //Successivamente, come nei casi precedenti, concateno le due monomial list a1 e b1 e infine richiamo il metodo functionOutputEqu passandogli la lista dei due elementi concatenati

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


