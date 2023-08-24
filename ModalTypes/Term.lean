import ModalTypes.Type
import ModalTypes.Context



inductive Term 
  | var : Nat → Term
  | lam : (t : Ty) → Term → Term
  | app : Term → Term → Term
  | pair : Term → Term → Term
  | inl : Term → Term
  | inr : Term → Term
  /-- open a box modality -/
  | open : Term → Term
  /-- shut a box modality -/
  | shut : Term → Term

-- inductive Term : Context → Ty → Type
--   | var : Var Γ t → Term Γ t
--   | lam : (t : Ty) → Term (t::Γ) u → Term Γ (.fun t u)
--   | prod : 