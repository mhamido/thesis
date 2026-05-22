Extending the arithmetic language with named exceptions.

\begin{code}
module Exceptions.Definitions where

open import Data.Bool hiding (T; if_then_else_) renaming (Bool to 𝔹)
open import Data.Nat

infixl 6 _⊞_
infix  0 if_then_else_
infix  0 try_catch_
\end{code}

\begin{code}
data Type : Set where
    Nat  : Type
    Bool : Type

⊨_ : Type → Set
⊨ Nat  = ℕ
⊨ Bool = 𝔹
\end{code}

\begin{code}
data Exception : Set where
    err : Exception
\end{code}

\begin{code}
data ⊢_ : Type → Set

variable
    T T₁ T₂ T₃ : Type
    n n₀ n₁ n₂ : ℕ
    v v₁ v₂ v₃ : ⊨ T
    e e₁ e₂ e₃ e' e₁' e₂' : ⊢ T
    ex          : Exception
    h           : Exception → ⊢ T
\end{code}

\begin{code}
data ⊢_ where
    `_            : ⊨ T → ⊢ T
    _⊞_           : ⊢ Nat → ⊢ Nat → ⊢ Nat
    test          : ⊢ Nat → ⊢ Bool
    if_then_else_ : ⊢ Bool → ⊢ T → ⊢ T → ⊢ T
    throw         : Exception → ⊢ T
    try_catch_    : ⊢ T → (Exception → ⊢ T) → ⊢ T

test' : ℕ → 𝔹
test' zero    = true
test' (suc n) = false
\end{code}
