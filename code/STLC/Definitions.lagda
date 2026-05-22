\begin{code}
module STLC.Definitions where

open import Data.Nat public
open import Data.Bool using (true; false; _∧_; _∨_; not) renaming (Bool to 𝔹) public

infixr 20 _⇒_
infixl 10 _·_
infixl 15 _⊞_
\end{code}

\begin{code}
data Type : Set where
    Bool : Type
    Nat  : Type
    _⇒_  : Type → Type → Type

open import Common.Context Type public
\end{code}

\begin{code}
variable
    Γ : Context
    T T₁ T₂ : Type

data _⊢_ : Context → Type → Set where
    Nat : ℕ → Γ ⊢ Nat
    _⊞_ : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Nat

    Bool : 𝔹 → Γ ⊢ Bool
    if_then_else_ : Γ ⊢ Bool → Γ ⊢ T → Γ ⊢ T → Γ ⊢ T
    
    Var : T ∈ Γ → Γ ⊢ T
    ƛ : (Γ , T₁) ⊢ T₂ → Γ ⊢ (T₁ ⇒ T₂)
    _·_ : Γ ⊢ (T₁ ⇒ T₂) → Γ ⊢ T₁ → Γ ⊢ T₂
\end{code}