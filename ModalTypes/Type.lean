import Mathlib.Data.Fin.Basic



inductive Modality
  | Box
  | Dia
  deriving Repr, DecidableEq

inductive TypeScheme (n : Nat)
  /-- `fun x y` is the type of functions from `x` to `y` -/
  | fun : TypeScheme n → TypeScheme n → TypeScheme n
  /-- `pair x y` is a pair of `x` and `y` -/
  | pair : TypeScheme n → TypeScheme n → TypeScheme n
  /-- `sum x y` is either an `x`, or a `y` -/
  | sum : TypeScheme n → TypeScheme n → TypeScheme n
  /-- `mod m x` is a type `x` under modality `m` -/
  | mod : Modality → TypeScheme n → TypeScheme n
  /-- A type variable -/
  | var : Fin n → TypeScheme n
  deriving Repr, DecidableEq

def Ty := TypeScheme 0

namespace TypeScheme

variable (f : Fin n → TypeScheme m) in
/-- Apply a transformation to variables, leaving other constructors unchanges -/
def substitute : TypeScheme n → TypeScheme m
  | .fun A B => .fun (substitute A) (substitute B)
  | .pair A B => .pair (substitute A) (substitute B)
  | .sum A B => .sum (substitute A) (substitute B)
  | .mod m A => .mod m (substitute A)
  | .var v => f v

def substituteAt (i : Fin (n+1)) (substituent : TypeScheme n) : TypeScheme (n+1) → TypeScheme n :=
  substitute <| match n with 
    -- if `n=0`, then there is only one possible variable `i : Fin (n+1)`, 
    -- So, we change all variables to the substituent
    | 0 => fun _ => substituent
    | _+1 => fun j => 
      if i = j then
        substituent
      else
        .var <| .predAbove (i.castPred) j

declare_syntax_cat mod_ty
scoped syntax "⟪" mod_ty "⟫" : term

syntax:46 mod_ty:45 " → " mod_ty:46 : mod_ty
syntax:56 mod_ty:56 " + " mod_ty:55 : mod_ty
syntax:66 mod_ty:66 " × " mod_ty:65 : mod_ty
syntax:99 "□" mod_ty:99 : mod_ty
syntax:99 "◇" mod_ty:99 : mod_ty
syntax "(" mod_ty ")" : mod_ty
syntax ident : mod_ty
syntax "%"term:100 : mod_ty

macro_rules
  | `(⟪ $A → $B ⟫) => `(TypeScheme.fun ⟪ $A ⟫ ⟪ $B ⟫)
  | `(⟪ $A × $B ⟫) => `(TypeScheme.pair ⟪ $A ⟫ ⟪ $B ⟫)
  | `(⟪ $A + $B ⟫) => `(TypeScheme.sum ⟪ $A ⟫ ⟪ $B ⟫)
  | `(⟪ □$A ⟫) => `(TypeScheme.mod .Box ⟪ $A ⟫)
  | `(⟪ ◇$A ⟫) => `(TypeScheme.mod .Dia ⟪ $A ⟫)
  | `(⟪ ($A) ⟫) => `(⟪$A⟫)
  | `(⟪ $A:ident ⟫) => `($A:term)
  | `(⟪ %$n:term ⟫) => `(TypeScheme.var $n)

end TypeScheme