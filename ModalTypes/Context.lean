import ModalTypes.Type

/-!
  In the paper, a context is presented as an (ordered) sequence of types and locks.
  We treat these locks as separators between sub-contexts consisting of just types,
  leading to a nested list
-/

abbrev Context : Type :=
  List (List Ty)

namespace Context

def add (t : Ty) : Context → Context
  | [] => [[t]]
  | Γ::Γs => (t::Γ)::Γs

def get? (Γ : Context) : (Nat × Nat) → Option Ty
  | ⟨i, j⟩ => List.get? Γ i |>.bind (List.get? · j)

def Var (Γ : Context) (ty : Ty) : Type :=
  { i // Γ.get? i = some ty}

end Context

export Context (Var)