(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Config.fs: configurazione statica
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Config

open System
open System.Reflection
open Prelude

let prompt_prefix = ">> "        

let prefix_max_len = 8

let exit_text = "quitting..."

let help_text = 
    let now = DateTime.Now
    let asm = Assembly.GetExecutingAssembly ()
    let name = asm.GetName ()
    let ver = name.Version
    let title = get_assembly_attribute<AssemblyTitleAttribute> asm
    let description = get_assembly_attribute<AssemblyDescriptionAttribute> asm
    let copyright = get_assembly_attribute<AssemblyCopyrightAttribute> asm
    let company = get_assembly_attribute<AssemblyCompanyAttribute> asm
    let credits =
        sprintf "%s v%d.%d.%d build %d [%04d-%02d-%02d]\n- %s\n%s, %s"
            title ver.Major ver.Minor ver.Build ver.Revision now.Year now.Month now.Day
            description copyright company
    sprintf """
CREDITS
%s

USAGE
Use this interactive console as a symbolic interpreter for polynomial expressions and equations.
Input must be a series of monomes of form Cx^N, where coefficient C is a signed rational number
and exponent N is a positive integer. The only recognized variable name is x.  
    
POLYNOMIALS
3x + 5x - 3 + 2                 this is recognized as a valid polynomial and normalization is performed
3x^3 - 5x^3 - 6                 powers can be written by suffixing ^N, where N is an integer
5x2 + 2x^2                      powers can also be shortcut by omitting the ^ character
6/7x - 4/9x                     rational coeffients are supported; powers cannot be rationals though
5x2 + -(-4x2 + -8x2)            parenthesization is supported
((5x2 - 2) + -(-4x + -8x)) + 8  even nested parentheses are
5x2 + (4x2 - 3) / (2x - 3)      this is NOT valid though: nesting of expressions is not supported

Putting the equality symbol between two polynomials turns the interpreter into an equation solver:

EQUATIONS
5x + 2x = 3x                this is recognized as an equation of degree 1 and gets solved in x
5x2 - 7x = 3                this is a degree-2 equation, yielding to up to 2 solutions
5/6x2 - 7x2 + 2 = x - 5     terms get first normalized and then roots are calculated
5x2 - 4x3 = 3x              degree-3 (or higher) equations are subject to normalization only; they do not get solved
x2 - (x2 + 3) = -3          degree is calculated after normalization: this is a degree-0 (constant) equation
3 - 2 = 4 - 1               degree-0 equations are treated as identities, either true or false

A polynomial can either be a plain polynomial or a derived polynomial:

DERIVATIVES
D[x2 - x + 2]               this derives the inner polynomial and produces the normalized polynomial as result
D[x2 - x + 2] = 2x - 2      deriving occurs before normalization, making this a degree-1 equation
D[x3 - 2x2] = D[x4 + 3]     both hands of an equation may contain derivatives
D[D[D[x3 - x2]]] = D[D[x4]] the derive operator can be recursive

Special commands for the intepreter start with '#', for example '#help'.
Here is a list of supported commands:

SPECIAL COMMANDS
#help                   show this help text
#exit                   quit the console (same as pressing Ctrl-C or typing command '#quit')
""" <| credits



