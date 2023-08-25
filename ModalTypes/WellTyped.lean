import ModalTypes.Term
import ModalTypes.Type
import ModalTypes.Context
import Aesop

open Ty 

@[aesop safe constructors]
inductive WellTyped : Context → Term → Ty → Prop
  /-- 
    The variable rule specifies we may only access variables to the right of the last lock.
    In our encoding, this means the variable must be in the last sub-context
  -/
  | var : Γ.get? x = some A → WellTyped (Γ::Γs) (.var x) A
  /-- Standard rule for lambdas -/
  | lam : WellTyped (Γ.add A) t B → WellTyped Γ (.lam A t) ⟪ A → B ⟫
  /-- Standard rule for application -/
  | app (A) : WellTyped Γ f ⟪ A → B⟫ → WellTyped Γ t A → WellTyped Γ (.app f t) B
  /-- Standard rule for products -/
  | prod : WellTyped Γ t A → WellTyped Γ u B → WellTyped Γ (.pair t u) ⟪ A × B ⟫
  /-- Standard rule for sums -/
  | inl : WellTyped Γ t A → WellTyped Γ (.inl t) ⟪ A + B ⟫
  /-- Standard rule for sums -/
  | inr : WellTyped Γ t B → WellTyped Γ (.inr t) ⟪ A + B ⟫
  | fst : WellTyped Γ t ⟪ A × B ⟫ → WellTyped Γ (.fst t) A
  | snd : WellTyped Γ t ⟪ A × B ⟫ → WellTyped Γ (.snd t) B
  /-
    TODO: in this encoding of the shut rule, `Γ'` cannot contain any more locks, but the original
      has no such restriction.
      We could turn this into `Γ' ++ Γ` with the restriction that `Γ' ≠ []`, or
        `Γs ++ (Γ'::Γ)` without such an extra assumption 
      (I choose this second option for now)
  -/
  | open : WellTyped Γ t ⟪ □A ⟫ → WellTyped (Γs ++ Γ'::Γ) (.open t) A
  | shut : WellTyped ([]::Γ) t A → WellTyped Γ (.shut t) ⟪ □A ⟫



example : ∃ t, WellTyped [] t ⟪ □(A → B) → □A → □B ⟫ := by
  refine ⟨
    .lam _ <| .lam _ <| .shut <| .app (.open <| .var 1) (.open <| .var 0),
    .lam <| .lam <| .shut ?h
  ⟩
  rw [←List.nil_append 
      ([] :: Context.add (mod Modality.Box A) (Context.add (mod Modality.Box (.fun A B)) []))]
  apply WellTyped.app A <;> {
    apply WellTyped.open
    apply WellTyped.var
    rfl
  }
