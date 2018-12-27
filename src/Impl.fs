
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

let rationalize (x : float) : rational =    
    let rec  aux (numero:float) (app:float) = if(numero*app%10.=0.) then rational(int(numero),int(app))
                                                                         else aux (numero*10.) (app*10.)
    in aux x 1.

let monomial_degree (m : monomial) : int = match m with (*all'oggetto monomio ottengo coefficente e grado e restituisco il grado*)
                                           Monomial(q,n) -> n
let monomial_negate (m : monomial) : monomial = match m with (*Dall'oggetto monomio ottengo coefficente e grado e restituisco il monomio negando il coefficente*)
                                                |Monomial(q,n) -> Monomial(-q,n)

let polynomial_degree (p : polynomial) : int =     
    let rec aux (gradoMassimo : int) (lst : polynomial) = match lst with (*Ricavo la lista di monomi dall'argomento p e confronto ad ogni chiamata l'esponente. Alla fine delle chiamate otterrò l'esponente maggiore*)
                                                          Polynomial([]) -> gradoMassimo
                                                          |Polynomial((Monomial(coeff,exp)) :: xs) -> if exp > gradoMassimo then aux exp (Polynomial(xs))
                                                                                                                else aux gradoMassimo (Polynomial(xs))
    in aux 0 p

let polynomial_negate (p : polynomial) : polynomial = match p with (*ricavo la lista di monomi dall'argomento e con la funzione List.map applico il cambio di segno a tutti i monomi della lista attraverso la funzione già creata*)
                                                      Polynomial lst -> Polynomial (List.map monomial_negate lst) 

let normalized_polynomial_degree (np : normalized_polynomial) : int = 
    match np with
    NormalizedPolynomial arr -> //Array.length (arr) (*ricavo l'array dall'argomento np e lo scorro contando gli elementi. il numero di elementi corrisponde al grado*)
                                let mutable count = 0 
                                for _ in arr do
                                    count <- count+1
                                count

let sumCoeffs (arr: rational[]) (pos:int) (coef:rational) : rational[] = 
    arr.[pos] <- arr.[pos]+coef (*se non funziona decomporre e fare la somma di frazioni*)
    arr
let normalize (p : polynomial) : normalized_polynomial = 
    (*STEPS:
        -> ricavare il grado del polinomio
        -> creare un array con numero di posti pari al grado del polinomio
        -> scorrere la lista (p) di monomi e controllarne il grado ad ogni iterazione. Quindi aggiornare la posizione dell'array (in posizione indicata dal grado del polinomio analizzato)
    *)  
    let risultati : rational[] = Array.create (polynomial_degree p) (rational(0,0))
        in
            let rec scorri (lst:polynomial) (risultati : rational[]) = match lst with
                                                                       Polynomial([]) -> risultati
                                                                       |Polynomial(Monomial(coeff,exp)::xs) -> scorri (Polynomial xs) (sumCoeffs risultati exp coeff)
            in scorri p risultati
    NormalizedPolynomial(risultati)

let derive (p : polynomial) : polynomial = raise (NotImplementedException ())
let reduce (e : expr) : polynomial = raise (NotImplementedException ())

let solve0 (np : normalized_polynomial) : bool = raise (NotImplementedException ())
let solve1 (np : normalized_polynomial) : rational = raise (NotImplementedException ())
let solve2 (np : normalized_polynomial) : (float * float option) option = raise (NotImplementedException ())





