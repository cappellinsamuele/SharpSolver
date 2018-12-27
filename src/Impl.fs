
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


let normalize (p : polynomial) : normalized_polynomial = raise (NotImplementedException ()) (*scorrere il polinomio e confrontare i gradi. Se trovo un grado che ho già trovato sommo i coefficienti. Alla fine ordino e metto tutti i coefficienti in un array NormalizedPolynomial*)
    (*let checkdeg (p:polynomial) (n:int) : bool = match p with //working on
                                                 
        in
             let rec degCount (p:polynomial) (count:int) : int = match p with
                                                                 |Polynomial([]) -> count
                                                                 |Polynomial ((Monomial(coef,exp))::xs) -> if (checkdeg p monomial_degree(Monomial(coef,exp))) then degCount (Polynomial(xs)) count else degCount (Polynomial(xs)) (count+1)
             in degCount p 0*)
                                       
let derive (p : polynomial) : polynomial = raise (NotImplementedException ())
let reduce (e : expr) : polynomial = raise (NotImplementedException ())

let solve0 (np : normalized_polynomial) : bool = raise (NotImplementedException ())
let solve1 (np : normalized_polynomial) : rational = raise (NotImplementedException ())
let solve2 (np : normalized_polynomial) : (float * float option) option = raise (NotImplementedException ())




