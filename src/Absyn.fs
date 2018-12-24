(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Absyn.fs: tipi base e AST
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Absyn  

open Prelude

// monomial and polynomial types
//

[< NoComparison >]
type monomial = Monomial of rational * int  // coefficient * degree
with    
    override this.ToString () =
        match this with
        | Monomial (q, _) when q = 0Q     -> "0"
        | Monomial (q, 1) when q = 1Q     -> "x"
        | Monomial (q, 1) when q = -1Q    -> "-x"
        | Monomial (x, 0)                 -> sprintf "%O" x
        | Monomial (x, 1)                 -> sprintf "%Ox" x
        | Monomial (q, n) when q = 1Q     -> sprintf "x^%d" n
        | Monomial (q, n) when q = -1Q    -> sprintf "-x^%d" n
        | Monomial (x, n)                 -> sprintf "%Ox^%d" x n

    static member Abs (Monomial (x, n)) = Monomial (abs x, n)
     
[< NoComparison >]
type polynomial = Polynomial of monomial list
with 
    override this.ToString () =
        let (Polynomial ms) = this
        let rec R = function 
            | [] -> "0"
            | [m : monomial] -> sprintf "%O" m
            | m1 :: (Monomial (x, _) as m2) :: ms -> sprintf "%O %c %s" m1 (if x >= 0Q then '+' else '-') (R (abs m2 :: ms))
        in
            R ms

[< NoComparison >]
type normalized_polynomial = NormalizedPolynomial of rational[]
with 
    override this.ToString () = 
        let (NormalizedPolynomial coeffs) = this
        in
            (Polynomial [ for deg = 0 to coeffs.Length - 1 do yield Monomial (coeffs.[deg], deg) ]).ToString ()


// top-level terms
//

[< NoComparison >]
type expr = Poly of polynomial
          | Derive of expr
with
    override this.ToString () = 
        match this with
        | Poly p        -> sprintf "%O" p
        | Derive e      -> sprintf "D[%O]" e

[< NoComparison >]
type line = Expr of expr
          | Equ of expr * expr
          | Cmd of string
with
    override this.ToString () = 
        match this with
        | Expr p        -> sprintf "%O" p
        | Equ (l, r)    -> sprintf "%O = %O" l r
        | Cmd s         -> sprintf "#%s" s
     