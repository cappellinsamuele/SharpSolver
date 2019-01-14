
(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Impl.fsi: implementazioni degli studenti
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Impl

open Absyn
open Prelude
open System
open System.Runtime.Remoting.Metadata.W3cXsd2001
open System

let rationalize (x : float) : rational =    //conversione dei float in rational con approccio aitmetico 
    let rec  aux (numero:float) (app:float) = if(numero*app%10.=0.) then rational(int(numero),int(app))
                                                                         else aux (numero*10.) (app*10.)
    in aux x 1.

let monomial_degree (m : monomial) : int = match m with //scompongo il parametro di tipo monomial m ottenendo coefficente e grado e restituisco il grado
                                           Monomial(_,deg) -> deg
let monomial_negate (m : monomial) : monomial = match m with //scompongo il parametro di tipo monomial m ottenendo coefficente e grado e restituisco il monomio negando il coefficente
                                                |Monomial(coef,deg) -> Monomial(-coef,deg)

let polynomial_degree (p : polynomial) : int =     
    let rec scan (gradoMassimo : int) (lst : polynomial) = match lst with //Ricavo la lista di monomi dall'argomento p e confronto ad ogni chiamata l'esponente corrente con il più alto trovato. Alla fine delle chiamate otterrò l'esponente maggiore
                                                           Polynomial([]) -> gradoMassimo
                                                           |Polynomial((Monomial(coeff,exp)) :: xs) -> if exp > gradoMassimo then scan exp (Polynomial(xs))
                                                                                                                else scan gradoMassimo (Polynomial(xs))
    in scan 0 p

let polynomial_negate (p : polynomial) : polynomial = match p with //ricavo la lista di monomi dall'argomento e con la funzione List.map applico il cambio di segno a tutti i monomi della lista attraverso la funzione creata in precedenza
                                                      Polynomial lst -> Polynomial (List.map monomial_negate lst) 

let normalized_polynomial_degree (np : normalized_polynomial) : int = 
    match np with
    NormalizedPolynomial arr -> //Array.length (arr) -1 //ricavo l'array dall'argomento np e lo scorro contando gli elementi. il numero di elementi corrisponde al grado del polinomio
                                let mutable count =  -1
                                for i in arr do
                                    count <- count+1
                                count

let sumCoeffs (coeffs: rational[]) (pos:int) (coef:rational) : rational[] = //Metodo usato in normalize per sommare i coefficienti dello stesso grado (quindi stessa posizione dell'array) restituendo un array
    coeffs.[pos] <- coeffs.[pos]+coef 
    coeffs
let normalize (p : polynomial) : normalized_polynomial = 
    (*STEPS:
        -> ricavare il grado del polinomio e creo un array con dimensione pari al grado del polinomio (con gli elementi a zero)
        -> scorrere la lista (p) di monomi e controllarne il grado ad ogni iterazione. Quindi aggiornare la posizione dell'array (in posizione indicata dal grado del polinomio analizzato)
    *)  
    let normalPol = Array.create (polynomial_degree p + 1) (rational.Zero)
        in
            let rec scan lst results = match lst with //scorro la lista di monomi contenuta in p e all'aaray results aggiungo il coefficiente nella posizone indicata dal grado del monomio
                                         Polynomial([]) -> results
                                         |Polynomial(Monomial(coeff,deg)::xs) -> scan (Polynomial xs) (sumCoeffs results deg coeff)
            in let a=scan p normalPol
    NormalizedPolynomial(normalPol) //ritorno un tipo NormalizedPolynomial


let derive (p : polynomial) : polynomial =
    match p with
    |Polynomial lst -> let rec scan (ls : monomial list) : monomial list = //scorro la lista. Ad ogni monomio contenuto nella lista il coefficiente viene moltiplicato per l'esponente e l'esponente viene abbassato di un grado
                            match ls with
                            |[] -> ls
                            |Monomial(coef,deg)::xs -> Monomial((rational((coef.N*deg),(coef.D))),(deg-1))::scan xs
                        in Polynomial(scan lst)

let rec sumZeros (p: polynomial) : polynomial = //metodo che serve a reduce per eliminare eventuali valori nulli dopo aver finito di ridurre/derivare il paramentro che le viene passato
    match p with
    Polynomial lst -> let rec scan (ls : monomial list) = //scorro la lista di monomi del polinomio. Se il coefficionte risulta essere 0 viene tolto dalla lista
                        match ls with
                        [] -> ls
                        |Monomial(coef,deg)::xs -> if (coef=rational.Zero) then scan xs else Monomial(coef,deg)::scan xs
                      in Polynomial(scan lst)                      
let rec countReduction (e:expr) = //metodo che serve a reduce per contare quante volte il processo di riduzione deve essere reiterato
    match e with
    |Poly pol -> 0                              //se trovo un polinomio posso ritornare
    |Derive der ->  1 + countReduction der      //se trovo un espressione derive vuol dire che devo aumentare il numero di riduzioni da effettuare
let rec extractPoly (e:expr) : polynomial = //metodo che serve a reduce per estrarre il polinomio più interno dell'espressione da derivare
    match e with
    |Poly p -> p                    //quando trovo il polinomio lo restituisco
    |Derive der -> extractPoly der  //se trovo un'espressione di tipo derive continuo a cercare al suo interno se cè un polinomio o se ci sono altre espressioni
let reduce (e : expr) : polynomial = 
    match e with 
    |Derive ex ->   let mutable countRed = countReduction ex //se trovo un tipo derive conto quante volte devo ridurre l'espressione (quindi dopo quante "D[" si trova il polinomio)
                    let mutable pol = extractPoly ex         //estraggo il polinomio da derivare contenuto all'interno dell'esspressione
                    while (countRed>=0) do                   //continuo a derivare il polinomio finché il contatore che indica quante volte derivare il polinomio arriva a 0
                            pol <- derive pol
                            countRed <- countRed-1
                    sumZeros(pol) //prima di ritornare il polinomio elimino gli elementi nulli
    |Poly p -> p //se trovo un polinomio lo ritorno subito 

let solve0 (np : normalized_polynomial) : bool = //ricavo l'array di rational dal parametro. Il polinomio associato sarà di grado 0 e verrà passato dal main come un unico polinomio 
    match np with
    NormalizedPolynomial arr -> arr.[0]=rational.Zero

let solve1 (np : normalized_polynomial) : rational = 
    match np with
    NormalizedPolynomial arr -> -(arr.[0]/arr.[1])

let solve2 (np : normalized_polynomial) : (float * float option) option = 
    match np with
    NormalizedPolynomial arr -> let delta = arr.[1]**2-rational(4,1)*arr.[2]*arr.[0]
                                    in 
                                        if (delta<rational.Zero) then None
                                        else 
                                            let x1 = ((-(rational.op_Implicit arr.[1]))+rational.Sqrt(delta))/2.*rational.op_Implicit arr.[2]
                                            let x2 = ((-(rational.op_Implicit arr.[1]))-rational.Sqrt(delta))/2.*rational.op_Implicit arr.[2]
                                                in
                                                    if (x1=x2) then Some(x1, None) 
                                                    else Some (x1, Some x2)

                                            





