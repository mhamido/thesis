module MiniSquared.BoolsTyped where

open import Data.Nat
open import Data.List
open import Data.Maybe
open import Data.Bool renaming (Bool to 𝔹) hiding (_<?_; T)

data ArithmeticOp : Set where
  ⊕ : ArithmeticOp

data CompareOp : Set where
  ≺ : CompareOp
  ≈ : CompareOp

data Type : Set where
  Nat  : Type
  Bool : Type

private variable
  T T' U V : Type
  n m  : ℕ
  b    : 𝔹

data ⊢_ : Type → Set where
  Num              : ℕ → ⊢ Nat
  _[_]ᵃ_           : ⊢ Nat → ArithmeticOp → ⊢ Nat → ⊢ Nat
  _[_]ᶜ_           : ⊢ Nat → CompareOp    → ⊢ Nat → ⊢ Bool
  False            : ⊢ Bool
  True             : ⊢ Bool
  if'_then'_else'_ : ⊢ Bool → ⊢ T → ⊢ T → ⊢ T

data Value : Type → Set where
  Nat  : ℕ → Value Nat
  Bool : 𝔹 → Value Bool

⟦_⟧ᵃ : ArithmeticOp → (ℕ → ℕ → ℕ)
⟦ ⊕ ⟧ᵃ = _+_

⟦_⟧ᶜ : CompareOp → (ℕ → ℕ → 𝔹)
⟦ ≺ ⟧ᶜ = _<ᵇ_
⟦ ≈ ⟧ᶜ = _≡ᵇ_

-- Index a frame by the hole's type and value it will produce
data Frame : Type → Type → Set where
  Binᵃ₁ : ArithmeticOp → ⊢ Nat → Frame Nat Nat
  Binᵃ₂ : Value Nat → ArithmeticOp → Frame Nat Nat
  Binᶜ₁ : CompareOp → ⊢ Nat → Frame Nat Bool
  Binᶜ₂ : Value Nat → CompareOp → Frame Nat Bool
  If₁   : ⊢ T → ⊢ T → Frame Bool T

-- Stack is indexed by the type of the top element and the
-- overall result type
data Stack : Type → Type → Set where
  ∅   : Stack T T
  _∷_ : Frame T U → Stack U V → Stack T V

-- State is indexed by the type of the overall result
data State : Type → Set where
  Eval : ⊢ T → Stack T V → State V
  Ret  : Value T → Stack T V → State V

step : State V -> State V
step (Eval (Num n) stack) = Ret (Nat n) stack
step (Eval (e₁ [ op ]ᵃ e₂) stack) = Eval e₁ (Binᵃ₁ op e₂ ∷ stack)
step (Eval (e₁ [ op ]ᶜ e₂) stack) = Eval e₁ (Binᶜ₁ op e₂ ∷ stack)
step (Eval False stack) = Ret (Bool false) stack
step (Eval True stack) = Ret (Bool true) stack
step (Eval (if' e₁ then' e₂ else' e₃) stack) = Eval e₁ (If₁ e₂ e₃ ∷ stack)
step (Ret v ∅) = Ret v ∅
step (Ret (Nat v₁) (Binᵃ₁ op e₂ ∷ stack)) = Eval e₂ (Binᵃ₂ (Nat v₁) op ∷ stack)
step (Ret (Nat v₂) (Binᵃ₂ (Nat v₁) op ∷ stack)) = Ret (Nat (⟦ op ⟧ᵃ v₁ v₂)) stack
step (Ret (Nat v₁) (Binᶜ₁ op e₂ ∷ stack)) = Eval e₂ (Binᶜ₂ (Nat v₁) op ∷ stack)
step (Ret (Nat v₂) (Binᶜ₂ (Nat v₁) op ∷ stack)) = Ret (Bool (⟦ op ⟧ᶜ v₁ v₂)) stack
step (Ret (Bool b) (If₁ e₂ e₃ ∷ stack)) = if b then Eval e₂ stack else Eval e₃ stack
