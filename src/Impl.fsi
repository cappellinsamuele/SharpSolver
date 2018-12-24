(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Impl.fsi: file di signature per le implementazioni degli studenti
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module SharpSolver.Impl

open Prelude
open Absyn

val rationalize : float -> rational

val monomial_degree : monomial -> int
val monomial_negate : monomial -> monomial
val polynomial_degree : polynomial -> int
val polynomial_negate : polynomial -> polynomial
val normalized_polynomial_degree : normalized_polynomial -> int

val normalize : polynomial -> normalized_polynomial
val derive : polynomial -> polynomial
val reduce : expr -> polynomial

val solve0 : normalized_polynomial -> bool
val solve1 : normalized_polynomial -> rational
val solve2 : normalized_polynomial -> (float * float option) option



