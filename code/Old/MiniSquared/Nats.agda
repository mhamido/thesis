module MiniSquared.Nats where

open import Data.Nat
open import Data.List

data Expr : Set where
  _N : ℕ → Expr
  _⊕_ : Expr → Expr → Expr

Value = ℕ

evaluate : Expr → Value
evaluate (x N) = x
evaluate (l ⊕ r) = evaluate l + evaluate r


data Frame : Set where
  Add₁ : Expr → Frame
  Add₂ : Value → Frame

data State : Set where
  Eval : Expr → List Frame → State
  Ret  : Value → List Frame → State

step : State → State
-- Evaluation
step (Eval (n N)   stack) = Ret n stack
step (Eval (l ⊕ r) stack) = Eval l (Add₁ r ∷ stack)
-- Returning
step (Ret v []) = Ret v []
step (Ret v₁ (Add₁ e₂ ∷ stack)) = Eval e₂ (Add₂ v₁ ∷ stack)
step (Ret v₂ (Add₂ v₁ ∷ stack)) = Ret (v₁ + v₂) stack
