module MiniSquared.Bools where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Bool renaming (Bool to 𝔹) hiding (_<?_)

-- Only a few binary operations for testing purposes
data Op : Set where
  Add : Op
  Lt  : Op
  Equ : Op

data Expr : Set where
  _N               : ℕ → Expr
  _[_]_            : Expr → Op → Expr → Expr
  False            : Expr
  True             : Expr
  if'_then'_else'_ : Expr → Expr → Expr → Expr

data Value : Set where
  Nat : ℕ → Value
  Bool : 𝔹 → Value

-- the 'primitive' function from the script
prim : Value -> Op -> Value -> Maybe Value
prim (Nat n₁) Add (Nat n₂) = just (Nat (n₁ + n₂))
prim (Nat n₁) Lt (Nat n₂) = just (Bool (n₁ <ᵇ n₂))
prim (Nat n₁) Equ (Nat n₂) = just (Bool (n₁ ≡ᵇ n₂))
prim (Bool _) _ _ = nothing
prim (Nat _) Add (Bool _) = nothing
prim (Nat _) Lt (Bool _) = nothing
prim (Nat _) Equ (Bool _) = nothing

data Frame : Set where
  Bin₁ : Op → Expr → Frame
  Bin₂ : Value → Op → Frame
  If₁  : Expr → Expr → Frame

data State : Set where
  Eval : Expr → List Frame → State
  Ret  : Value → List Frame → State

step : State → Maybe State
-- Evaluation
step (Eval (n N) stack) = just (Ret (Nat n) stack)
step (Eval (e₁ [ ⊕ ] e₂) stack) = just (Eval e₁ (Bin₁ ⊕ e₂ ∷ stack))
step (Eval False stack) = just (Ret (Bool false) stack)
step (Eval True stack) = just (Ret (Bool true) stack)
step (Eval (if' e₁ then' e₂ else' e₃) stack) = just (Eval e₁ ((If₁ e₂ e₃) ∷ stack))
-- Returning
step (Ret v []) = just (Ret v [])
step (Ret v₁ (Bin₁ ⊕ e₂ ∷ stack)) = just (Eval e₂ (Bin₂ v₁ ⊕ ∷ stack))
step (Ret v₂ (Bin₂ v₁ ⊕ ∷ stack)) with prim v₁ ⊕ v₂
... | just v  = just (Ret v stack)
... | nothing = nothing
step (Ret (Bool b) (If₁ e₂ e₃ ∷ stack)) = if b then just (Eval e₂ stack) else just (Eval e₃ stack)
step (Ret (Nat _)  (If₁ e₂ e₃ ∷ stack)) = nothing
