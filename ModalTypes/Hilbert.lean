import ModalTypes.Type
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
  | axiom : (∃i, axioms.get i = ⟨n, t⟩) → Proof axioms t
  | modusPonens {A B : TypeScheme n} : 
      Proof axioms ⟪A → B⟫ → Proof axioms A → Proof axioms B
  | substitution (f : Fin n → TypeScheme m) : Proof axioms A → Proof axioms (A.substitute f)
  /--
    Rule of necessitation: if `A` is a theorem, then so is `□A`.
    Note that this is different from having `A → □A` as an axiom!
  -/
  | necessitation : Proof axioms A → Proof axioms ⟪ □A ⟫



/-- The basic axioms of propositional, intuitionistic logic 
    https://en.wikipedia.org/wiki/Intuitionistic_logic
-/
def propLogic : Axioms := [
  ⟨2, ⟪ %0 → %1 → %0 ⟫⟩,  -- THEN-1
  ⟨3, ⟪ (%0 → (%1 → %2)) → (%0 → %1) → (%0 → %2) ⟫⟩, -- THEN-2
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

end Axioms