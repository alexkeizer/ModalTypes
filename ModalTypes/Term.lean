import ModalTypes.Type
import ModalTypes.Context



inductive Term 
  | var : Nat → Term
  | lam : (t : Ty) → Term → Term
  | app : Term → Term → Term
  | pair : Term → Term → Term
  | inl : Term → Term
  | inr : Term → Term
  | fst : Term → Term
  | snd : Term → Term
  | case (t u₁ u₂ : Term) : Term
  /-- open a box modality -/
  | open : Term → Term
  /-- shut a box modality -/
  | shut : Term → Term




namespace Term

/-- 
  A term is closed if it has no free variables. 
  Auxiliary definition where variables strictly less than `b` are considered bound 
-/
def IsClosedUpTo (b : Nat) : Term → Prop
  | var n         => n < b
  | lam _ t       => IsClosedUpTo (b+1) t
  | app t u       => IsClosedUpTo b t ∧ IsClosedUpTo b u
  | pair t u      => IsClosedUpTo b t ∧ IsClosedUpTo b u
  | inl t         => IsClosedUpTo b t
  | inr t         => IsClosedUpTo b t
  | fst t         => IsClosedUpTo b t
  | snd t         => IsClosedUpTo b t
  | case t u₁ u₂  => IsClosedUpTo b t ∧ IsClosedUpTo (b+1) u₁ ∧ IsClosedUpTo (b+1) u₂
  | «open» t      => IsClosedUpTo b t
  | shut t        => IsClosedUpTo b t

/-- A term is closed if it has no free variables -/
abbrev IsClosed : Term → Prop := IsClosedUpTo 0



theorem isClosedUpTo_succ {t : Term} : t.IsClosedUpTo n → t.IsClosedUpTo (n+1) := by
  intro h
  induction t generalizing n <;> simp_all [IsClosedUpTo]
  . apply Nat.lt_add_right _ _ _ h

theorem isClosedUpTo_add {t : Term} : t.IsClosedUpTo n → t.IsClosedUpTo (n+m) := by
  intro h
  induction m
  next    => exact h
  next ih => apply isClosedUpTo_succ ih


end Term