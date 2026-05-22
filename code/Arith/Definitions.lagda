\begin{code}
module Arith.Definitions where

open import Data.Bool hiding (T; if_then_else_) renaming (Bool to 𝔹)
open import Data.Nat

infixl 6 _⊞_
infix  0 if_then_else_
\end{code}

\begin{code}
data Type : Set where
    Nat : Type
    Bool : Type

⊨_ : Type → Set
⊨ Nat       = ℕ
⊨ Bool      = 𝔹
\end{code}

\begin{code}

data ⊢_ : Type → Set

variable
    T T₁ T₂ T₃ : Type
    n n₀ n₁ n₂ : ℕ
    v v₁ v₂ v₃ : ⊨ T
    e e₁ e₂ eᶜ : ⊢ T
\end{code}

\begin{code}
data ⊢_ where
    `_ : ⊨ T → ⊢ T
    _⊞_ :  ⊢ Nat → ⊢ Nat → ⊢ Nat
    test : ⊢ Nat → ⊢ Bool
    if_then_else_ : ⊢ Bool → ⊢ T → ⊢ T → ⊢ T

test' : ℕ → 𝔹
test' zero    = true
test' (suc n) = false
\end{code}