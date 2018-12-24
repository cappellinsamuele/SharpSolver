(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Prelude.fs: definizinoni iniziali
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Prelude

open System

// misc stuff
//

let parse_float s = Double.Parse (s, Globalization.NumberStyles.Float, Globalization.CultureInfo.InvariantCulture)   

let get_assembly_attribute<'T when 'T :> System.Attribute> (asm : System.Reflection.Assembly) =
    let t = typeof<'T>
    try
        let rex = new Text.RegularExpressions.Regex ("(System.Reflection.Assembly)(\w+)(Attribute)")
        let name = rex.Match(t.FullName).Groups.[2].Value
        let atts = asm.GetCustomAttributes (t, false)
        let att = atts.[0] :?> System.Attribute
        in
            att.GetType().GetProperty(name).GetValue(att, [||]).ToString ()
    with _ -> ""



// rationals
//

[<StructuredFormatDisplayAttribute("{AsString}")>]
type rational (p : int, ?q : int) =
    let q = defaultArg q 1

    let rec gcd a (b : int) = if b = 0 then a else gcd b (a % b)

    let fix_sign (p : int, q : int) =  if q > 0 then p, q else -p, -q

    let p, q =
        if q = 0 then raise (System.DivideByZeroException ())
        let g = gcd q p
        fix_sign (p / g, q / g)

    static member One = rational (1, 1)
    static member Zero = rational (0, 1)
    
    static member Parse (s : string) =
        match s.Split [|'/'|] with
        | [|n; d|] -> rational (Int32.Parse n, Int32.Parse d)
        | _        -> failwithf "rational.Parse: invalid syntax: %s" s

    member __.N = p
    member __.D = q

    static member Sqrt (m : rational) : float = sqrt (float m)

    member this.AsString = this.ToString ()
    override __.ToString () =
        if q = 1 then p.ToString () else sprintf "%A/%A" p q

    interface System.IEquatable<rational> with
        member q1.Equals q2 = q1.N = q2.N && q1.D = q2.D

    override q1.Equals q2 = (q1 :> System.IEquatable<_>).Equals(q2 :?> rational)

    interface System.IComparable<rational> with
        member q1.CompareTo q2 = compare (q1.N * q2.D) (q2.N * q1.D)

    interface System.IComparable with
        member q1.CompareTo q2 = (q1 :> System.IComparable<_>).CompareTo (q2 :?> rational)

    override q.GetHashCode() = hash (q.N, q.D)

    static member Abs (m : rational) = rational (abs m.N, abs m.D)    // needed by F# constrained polymorphic function 'abs'

    static member Pow (m : rational, e : int) = 
        if e = 0 then rational.One
        elif e = 1 then m
        else m * rational.Pow (m, e - 1)

    static member (+) (m : rational, n : rational) = rational (m.N * n.D + n.N * m.D, m.D * n.D)
    static member (-) (m : rational, n : rational) = rational (m.N * n.D - n.N * m.D, m.D * n.D)
    static member (~-) (m : rational) = rational (-m.N, m.D)
    static member (*) (m : rational, n : rational) = rational (m.N * n.N, m.D * n.D)
    static member (/) (m : rational, n : rational) = rational (m.N * n.D, m.D * n.N)

    static member op_Implicit (a : rational) : float = float a.N / float a.D


[<AutoOpen>]
module NumericLiteralQ =
    let FromZero () = rational.Zero
    let FromOne ()  = rational.One
    let FromInt32 (n : int32) = rational (int n)
    let Fromint (n : int) = rational n
    let FromString (s : string) = rational (Int32.Parse s)

        
module LexYacc =
    open Microsoft.FSharp.Text

    exception ParseErrorContextException of obj

    let parse_error_rich = Some (fun ctx -> raise (ParseErrorContextException ctx))
    let newline (lexbuf : Lexing.LexBuffer<_>) = lexbuf.EndPos <- lexbuf.EndPos.NextLine    
    let lexeme = Lexing.LexBuffer<_>.LexemeString
    let trim c lexbuf = let s = lexeme lexbuf in s.TrimStart [|c|] 


