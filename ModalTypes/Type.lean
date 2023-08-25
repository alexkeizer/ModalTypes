


inductive Modality
  | Box
  | Dia

inductive Ty
  /-- `fun x y` is the type of functions from `x` to `y` -/
  | fun : Ty → Ty → Ty
  /-- `pair x y` is a pair of `x` and `y` -/
  | pair : Ty → Ty → Ty
  /-- `sum x y` is either an `x`, or a `y` -/
  | sum : Ty → Ty → Ty
  /-- `mod m x` is a type `x` under modality `m` -/
  | mod : Modality → Ty → Ty


namespace Ty

declare_syntax_cat mod_ty
scoped syntax "⟪" mod_ty "⟫" : term

syntax:66 mod_ty:65 " → " mod_ty:66 : mod_ty
syntax mod_ty " + " mod_ty : mod_ty
syntax mod_ty " × " mod_ty : mod_ty
syntax:99 "□" mod_ty:100 : mod_ty
syntax:99 "◇" mod_ty:100 : mod_ty
syntax "(" mod_ty ")" : mod_ty
syntax ident : mod_ty

macro_rules
  | `(⟪ $A → $B ⟫) => `(Ty.fun ⟪ $A ⟫ ⟪ $B ⟫)
  | `(⟪ $A × $B ⟫) => `(Ty.pair ⟪ $A ⟫ ⟪ $B ⟫)
  | `(⟪ $A + $B ⟫) => `(Ty.sum ⟪ $A ⟫ ⟪ $B ⟫)
  | `(⟪ □$A ⟫) => `(Ty.mod .Box ⟪ $A ⟫)
  | `(⟪ ◇$A ⟫) => `(Ty.mod .Dia ⟪ $A ⟫)
  | `(⟪ ($A) ⟫) => `(⟪$A⟫)
  | `(⟪ $A:ident ⟫) => `($A:term)
  

end Ty