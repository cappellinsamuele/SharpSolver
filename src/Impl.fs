
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

let monomial_degree (m : monomial) : int = match m with
                                           Monomial(q,n) -> n
let monomial_negate (m : monomial) : monomial = match m with
                                                |Monomial(q,n) -> Monomial(-q,n)

let polynomial_degree (p : polynomial) : int =     
    let rec aux (gradoMassimo : int) (lst : polynomial) = match lst with
                                                          Polynomial([]) -> gradoMassimo
                                                          |Polynomial((Monomial(coeff,exp)) :: xs) -> if exp > gradoMassimo then aux exp (Polynomial(xs))
                                                                                                                else aux gradoMassimo (Polynomial(xs))
    in aux 0 p

let polynomial_negate (p : polynomial) : polynomial = match p with
                                                      Polynomial lst -> Polynomial (List.map monomial_negate lst)

let normalized_polynomial_degree (np : normalized_polynomial) : int = 
    let mutable count = 0
        in
        for _ in np do
           count <- count+1
    count


        


let normalize (p : polynomial) : normalized_polynomial = raise (NotImplementedException ())
let derive (p : polynomial) : polynomial = raise (NotImplementedException ())
let reduce (e : expr) : polynomial = raise (NotImplementedException ())

let solve0 (np : normalized_polynomial) : bool = raise (NotImplementedException ())
let solve1 (np : normalized_polynomial) : rational = raise (NotImplementedException ())
let solve2 (np : normalized_polynomial) : (float * float option) option = raise (NotImplementedException ())




