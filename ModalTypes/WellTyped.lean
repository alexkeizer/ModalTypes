import ModalTypes.Term
import ModalTypes.Type
import ModalTypes.Context
import ModalTypes.Hilbert
import Aesop

open TypeScheme -- for notation

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
  | pair : WellTyped Γ t A → WellTyped Γ u B → WellTyped Γ (.pair t u) ⟪ A × B ⟫
  /-- Standard rule for sums -/
  | inl : WellTyped Γ t A → WellTyped Γ (.inl t) ⟪ A + B ⟫
  /-- Standard rule for sums -/
  | inr : WellTyped Γ t B → WellTyped Γ (.inr t) ⟪ A + B ⟫
  | fst : WellTyped Γ t ⟪ A × B ⟫ → WellTyped Γ (.fst t) A
  | snd : WellTyped Γ t ⟪ A × B ⟫ → WellTyped Γ (.snd t) B
  | case : WellTyped Γ t ⟪ A + B ⟫ → WellTyped (Γ.add A) u₁ C → WellTyped (Γ.add B) u₂ C
    → WellTyped Γ (.case t u₁ u₂) C
  /-
    TODO: in this encoding of the shut rule, `Γ'` cannot contain any more locks, but the original
      has no such restriction.
      We could turn this into `Γ' ++ Γ` with the restriction that `Γ' ≠ []`, or
        `Γs ++ (Γ'::Γ)` without such an extra assumption 
      (I choose this second option for now)
  -/
  | open : WellTyped Γ t ⟪ □A ⟫ → WellTyped (Γs ++ Γ'::Γ) (.open t) A
  | shut : WellTyped Γ.addLock t A → WellTyped Γ (.shut t) ⟪ □A ⟫


namespace WellTyped

notation Γ " ⊢ " t " : " A => WellTyped Γ t A
notation "⊢ " t " : " A => WellTyped [] t A



/-
  # Completeness
-/

open Axioms (K Proof THEN₁)

namespace Completeness

abbrev Inhabited (A : Ty) : Prop :=
  ∃t, ⊢ t : A 

theorem THEN₁ : Inhabited ⟪ A → B → A ⟫ := ⟨
    .lam A <| .lam B <| .var 1, 
    .lam <| .lam <| .var rfl
  ⟩

theorem THEN₂ : Inhabited ⟪ (A → B → C) → (A → B) → (A → C) ⟫ := ⟨
    .lam ⟪A → B → C⟫ <| .lam ⟪A → B⟫ <| .lam A <| .app 
      (.app (.var 2) (.var 0)) 
      (.app (.var 1) (.var 0)), 
    by
      apply lam <| lam <| lam _
      apply app
      . apply app
        . apply var; rfl
        . apply var; rfl
      . apply app
        . apply var; rfl
        . apply var; rfl
  ⟩

theorem AND₁ : Inhabited ⟪ A × B → A ⟫ := ⟨
  .lam ⟪A × B⟫ <| .fst <| .var 0,
  lam <| fst <| var rfl
⟩

theorem AND₂ : Inhabited ⟪ A × B → B ⟫ := ⟨
  .lam ⟪A × B⟫ <| .snd <| .var 0,
  lam <| snd <| var rfl
⟩

theorem AND₃ : Inhabited ⟪ A → B → A × B ⟫ := ⟨
  .lam A <| .lam B <| .pair (.var 1) (.var 0),
  by 
    apply lam <| lam <| pair _ _
    <;> apply var (by rfl)
⟩

theorem OR₁ : Inhabited ⟪ A → A + B ⟫ := ⟨
  .lam A <| .inl (.var 0),
  lam <| inl <| var rfl
⟩

theorem OR₂ : Inhabited ⟪ B → A + B ⟫ := ⟨
  .lam B <| .inr (.var 0),
  lam <| inr <| var rfl
⟩

theorem OR₃ : Inhabited ⟪ (A → C) → (B → C) → A + B → C ⟫ := ⟨
  .lam ⟪A → C⟫ <| .lam ⟪B → C⟫ <| .lam ⟪A+B⟫ <| .case (.var 0) 
    (.app (.var 3) (.var 0))
    (.app (.var 2) (.var 0)),
  lam <| lam <| lam <| case (var rfl) (app _ (var rfl) (var rfl)) (app _ (var rfl) (var rfl))
⟩

theorem K : Inhabited ⟪ □(A → B) → □A → □B ⟫ := by
  refine ⟨
    .lam _ <| .lam _ <| .shut <| .app (.open <| .var 1) (.open <| .var 0),
    .lam <| .lam <| .shut ?h
  ⟩
  rw [Context.addLock, ←List.nil_append 
      ([] :: Context.add (mod Modality.Box A) (Context.add (mod Modality.Box (.fun A B)) []))]
  apply WellTyped.app A <;> {
    apply WellTyped.open
    apply WellTyped.var
    rfl
  }

end Completeness

/-- If a term is welltyped under an empty context, then it is closed -/
theorem closed_of_wellTyped_empty : (⊢ t : A) → t.IsClosed := by
  simp only [Term.IsClosed]
  suffices ∀ Γ,
    (Γ ⊢ t : A) → (Term.IsClosedUpTo Γ.vars t)
  from this []
  intro Γ h
  induction h
  <;> simp_all [Term.IsClosedUpTo, Context.addLock]
  next h => 
    rcases List.get?_eq_some.mp h with ⟨h_lt, _⟩
    apply Nat.lt_add_right _ _ _ h_lt
  next ih =>
    rw [Nat.add_comm, Nat.add_comm (List.length _), Nat.add_assoc]
    apply Term.isClosedUpTo_add ih


/-- Rule of necessitation -/
theorem weaken_addLock_of_closed {t : Term} : (Γ ⊢ t : A) → ((Γ.concat []) ⊢ t : A) := by
  intro h_wt
  induction h_wt 
  case var h => apply var h
  case lam h ih =>
    -- rw [Context.add] at ih
    apply lam
    apply ih
    


-- theorem weakenOne : (Γ ⊢ t : A) → (Γ' :: Γ) ⊢ t : A := by
--   sorry

-- theorem weaken (Γ' : Context) : (Γ ⊢ t : A) → (Γ' ++ Γ) ⊢ t : A := by
--   intro h
--   induction Γ'
--   next => exact h
--   next Γ'₀  Γ' ih =>
--     have := weakenOne Γ'₀ ih

/-- Show that every theorem of the axiomatic proof system is inhabited -/
theorem complete : K.Proof A → (∃ t, ⊢ t : A) := by
  suffices ∀ {n} (A : TypeScheme n) (f : Fin n → Ty),
    K.Proof A → (∃t, ⊢ t : (A.substitute f)  )
  by
    intro h
    specialize this A Fin.elim0 h
    simp at this
    exact this
  intro n A f h
  induction h
  case «axiom» h =>
    rcases h with ⟨⟨⟩|⟨⟩|⟨⟩|⟨⟩|⟨⟩|⟨⟩|⟨⟩|⟨⟩|⟨⟩|⟨⟩, h⟩ 
    <;> simp[List.get?] at h
    <;> (try rcases h with ⟨⟨⟩, ⟨⟩⟩)
    . apply Completeness.THEN₁
    . apply Completeness.THEN₂
    . apply Completeness.AND₁
    . apply Completeness.AND₂
    . apply Completeness.AND₃
    . apply Completeness.OR₁
    . apply Completeness.OR₂
    . apply Completeness.OR₃
    . apply Completeness.K
  case substitution g h_eq ih => 
    specialize ih (fun i => (g i).substitute f)
    rw [←TypeScheme.substitute_substitute, h_eq] at ih
    apply ih
  case necessitation ih => 
    simp [substitute]
    rcases ih f with ⟨t, ih⟩
    use .shut t
    apply shut
  case modusPonens =>
    sorry


/-
  # Soundness
-/
-- theorem sound : (∃ t, Γ ⊢ t : A) → K.Proof ⟦ Γ ⊢ _ : A ⟧ := by
--   rintro ⟨t, h⟩
--   induction h
--   next Γ Γs v hv =>
--     cases Γ
--     next => contradiction
--     next Γ_hd Γ_tl =>
--       simp only [Context.denote]
--       induction v
--       next =>
--         simp at hv
--         subst hv
--         apply THEN₁.substitution (fun
--             | (0 : Fin 2) => Γ_hd
--             | (1 : Fin 2) => ⟦ Γ_tl :: Γs ⊢ _ : Γ_hd ⟧
--           )
--         rfl
--       next =>
--         sorry
--   next =>
--     sorry
--   next =>
--     sorry
--   next =>
--     sorry
--   next =>
--     sorry
--   next =>
--     sorry
--   next =>
--     sorry
--   next =>
--     sorry
--   next =>
--     sorry
--   next =>
--     sorry

end WellTyped