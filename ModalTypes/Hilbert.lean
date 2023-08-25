import ModalTypes.Type
import Mathlib.Data.Vector.Basic

def TypeScheme : Nat → Type
  | 0 => Ty
  | n+1 => Ty → TypeScheme n

def TypeScheme.apply (t : TypeScheme n) (args : Vector Ty n) : Ty :=
  by 
    cases args using Vector.inductionOn
    next => exact t -- nil
    next x args _ => exact apply (t x) args -- cons


namespace HilbertProof


inductive Hypothesis (Γ : List (Σn, TypeScheme n)) (t : ) : Type
  /-- An axiom -/
  | axiomI (i : Fin ax)
  /-- A previously proven result -/
  | prevI (i : Fin n)

inductive Proof (ax n : Nat)
  /-- substitution -/
  | sub {m} (scheme : Index ax n) (sub : Vector (Index ax n) m)

end HilbertProof


/--
  Treating types just as formulas, a `HilbertProof t` shows that `t` is an axiom.
  A proof is 
-/
inductive HilbertProof : List (Σn, TypeScheme n) → TypeScheme n → Prop
  | quantify (t : TypeScheme (n+1)) : (∀ u, HilbertProof <| t u) → HilbertProof t 
  | 