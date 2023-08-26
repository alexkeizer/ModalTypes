import ModalTypes.Type
import ModalTypes.Context
import Mathlib.Data.Vector.Basic

open TypeScheme

abbrev Axioms := List (Σn, TypeScheme n)

namespace Axioms

/--
  Treating types just as formulas, a `Proof axioms t` shows that `t` is a theorem that follows
  from the given `axioms`.
  This is a Hilbert-style axiomatic proof.
-/
inductive Proof (axioms : Axioms) : {n : Nat} → TypeScheme n → Prop
  | axiom : (∃i, axioms.get? i = some ⟨n, A⟩) → Proof axioms A
  | modusPonens {A B : TypeScheme n} : 
      Proof axioms ⟪A → B⟫ → Proof axioms A → Proof axioms B
  | substitution ⦃n : Nat⦄ {A : TypeScheme n} (h : Proof axioms A)
      (f : Fin n → TypeScheme m) (h_eq : A.substitute f = A' := by rfl) : 
      Proof axioms A'
  /--
    Rule of necessitation: if `A` is a theorem, then so is `□A`.
    Note that this is different from having `A → □A` as an axiom!
  -/
  | necessitation : Proof axioms A → Proof axioms ⟪ □A ⟫


/-
  # Axiom Sets
-/

/-- The basic axioms of propositional, intuitionistic logic 
    https://en.wikipedia.org/wiki/Intuitionistic_logic
-/
def propLogic : Axioms := [
  ⟨2, ⟪ %0 → %1 → %0 ⟫⟩,  -- THEN-1
  ⟨3, ⟪ (%0 → %1 → %2) → (%0 → %1) → (%0 → %2) ⟫⟩, -- THEN-2
  ⟨2, ⟪ %0 × %1 → %0 ⟫⟩, -- AND-1
  ⟨2, ⟪ %0 × %1 → %1 ⟫⟩, -- AND-2
  ⟨2, ⟪ %0 → %1 → %0 × %1 ⟫⟩, -- AND-3
  ⟨2, ⟪ %0 → %0 + %1 ⟫⟩, -- OR-1
  ⟨2, ⟪ %1 → %0 + %1 ⟫⟩, -- OR-2
  ⟨2, ⟪ (%0 → %2) → (%1 → %2) → (%0 + %1 → %2)⟫⟩ -- OR-3
  -- no False, since we don't have an empty type
]

def K : Axioms := propLogic ++ [
  ⟨2, ⟪ □(%0 → %1) → □%0 → □%1 ⟫⟩
]

/-
  # Theorems
-/

/-- Adding more axioms does not invalidate earlier theorems -/
theorem Proof.append_axioms (h : Proof axioms A) : Proof (axioms ++ newAxioms) A := by
  induction h
  next h =>
    apply Proof.axiom
    rcases h with ⟨i, h⟩
    use i
    rw [List.get?_append (List.get?_eq_some.mp h).1]
    apply h
  next ih₁ ih₂ => apply Proof.modusPonens ih₁ ih₂
  next f h_eq ih => apply ih.substitution f h_eq
  next ih => apply Proof.necessitation ih

theorem THEN₁ : Proof propLogic (n:=2) ⟪ %0 → %1 → %0 ⟫ :=
  .axiom ⟨0, rfl⟩

theorem THEN₂ : Proof propLogic (n:=3) ⟪ (%0 → %1 → %2) → (%0 → %1) → (%0 → %2) ⟫ :=
  .axiom ⟨1, rfl⟩

theorem OR₁ : Proof propLogic (n:=2) ⟪ %0 → %0 + %1 ⟫ :=
  .axiom ⟨5, rfl⟩

theorem THEN_id : Proof propLogic (n:=1) ⟪ %0 → %0 ⟫ :=
  have t₁ := THEN₁.substitution (m:=1) (fun 
      | 0 => ⟪%0⟫
      | 1 => ⟪%0 + %0⟫
    )
  have t₂ := THEN₂.substitution (m:=1) (fun
      | 0 => ⟪%0⟫
      | 1 => ⟪%0 + %0⟫
      | 2 => ⟪%0⟫
    )
  have o₁ := OR₁.substitution (m:=1) (fun _ => ⟪%0⟫)
  .modusPonens (t₂.modusPonens t₁) o₁

-- theorem THEN_a_to_b_to_c :Proof propLogic (n:=3) ⟪(%0 → %2) → %0 → %1 → %2⟫ := by
--   -- have t : Proof _ ⟪ (%0 → %0 → %1 → %2) → (%0 → %0) → (%0 → %1 → %2) ⟫ := THEN₂.substitution (m:=3) (fun
--   --   | 0 => ⟪ %0 ⟫
--   --   | 1 => ⟪ %0 ⟫
--   --   | 2 => ⟪ %1 → %2 ⟫
--   -- ) 
--   sorry

-- theorem implication (h : Proof ax A → Proof Ax B) : Proof ax ⟪ A → B ⟫ := by
--   sorry

/-
  # Context denotation
-/

-- open Proof in
-- theorem denote_ofResult : Proof K ⟪A → ${⟦ Γ ⊢ _ : A ⟧}⟫ := by
--   induction Γ
--   next => 
--     exact THEN_id.append_axioms.substitution (fun _ => A)
--   next Γ Γs ih =>
--     induction Γ <;> simp only [Context.denote]
--     next => 
--       -- apply Proof.necessitation ih
--       sorry
--     next hd tl ih₂ =>
--       apply Proof.modusPonens _ ih₂
--       -- apply THEN₁.append_axioms.substitution (fun
--       --     | 0 => ⟦ tl :: Γs ⊢ _ : A ⟧
--       --     | 1 => hd
--       --   )
--       sorry
      

end Axioms