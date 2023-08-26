import ModalTypes.Type
import Mathlib.Tactic.Linarith

/-!
  In the paper, a context is presented as an (ordered) sequence of types and locks.
  We treat these locks as separators between sub-contexts consisting of just types,
  leading to a nested list
-/

abbrev Context : Type :=
  List (List Ty)

namespace Context

/-- 
  Add a new variable to the top-most sub-context, 
  creating a new sub-context if none exists yet -/
def add (t : Ty) : Context → Context
  | [] => [[t]]
  | Γ::Γs => (t::Γ)::Γs

/--
  Add a new lock to the context
-/
def addLock : Context → Context :=
  fun Γ => []::Γ

def get? (Γ : Context) : (Nat × Nat) → Option Ty
  | ⟨i, j⟩ => List.get? Γ i |>.bind (List.get? · j)

def Var (Γ : Context) (ty : Ty) : Type :=
  { i // Γ.get? i = some ty}

/-- 
  The total number of vars in this context.
  That is, the sum of the number of vars in each sub-context, disregarding the locks
-/
def vars : Context → Nat :=
  Nat.sum ∘ List.map (List.length)

open TypeScheme in
/--
  Given a context `Γ` and an expected type `A`, we can determine the denotation of a judgement
    `Γ ⊢ _ : A`
  as a formula (type)
  Note that this denotation depends only on `Γ` and `A`, not on the structure of the proof, hence
  it is defined here.
-/
def denote : Context → Ty → Ty
  | [],           A => A
  | (B::Bs)::Γs,  A => ⟪B → ${denote (Bs::Γs) A}⟫
  | []::Γs,       A => ⟪ □${denote Γs A} ⟫

notation (priority := high) "⟦ " Γ " ⊢ _ : " t " ⟧" => denote Γ t 




/-
  ## Theorems
-/

@[simp]
theorem vars_add :
    vars (add A Γ) = vars Γ + 1 := by
  simp only [vars, add, Function.comp]
  cases Γ 
  . rfl
  . simp only [List.map, List.length_cons, Nat.sum_cons]; linarith

@[simp]
theorem vars_cons :
    vars (Γ :: Γs) = Γ.length + vars Γs := by
  rfl

@[simp]
theorem vars_append :
    vars (Γ ++ Γ') = vars Γ + vars Γ' := by
  simp only [vars, Function.comp_apply, List.map_append, Nat.sum_append]

end Context

export Context (Var)