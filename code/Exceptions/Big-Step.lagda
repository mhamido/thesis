Big-step semantics for the arithmetic language with exceptions.
Terms evaluate to either a value (return) or an exception (raise).

\begin{code}
module Exceptions.Big-Step where

open import Exceptions.Definitions public
open import Data.Nat

open import Data.Bool hiding (T; if_then_else_) renaming (Bool to 𝔹)
open import Data.Product using (∃) renaming (_,_ to _﹐_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_) renaming (refl to reflexive)
\end{code}

A result is either a returned value or a raised exception.

\begin{code}
-- Note: Could also use the _⊎_ type from the stdlib, but then a lot of this would have to be type annotated.
data Result (T : Type) : Set where
    return : ⊨ T → Result T
    raise  : Exception → Result T

variable
    r r₁ r₂ : Result T
\end{code}

\begin{code}
infix 3 _⇓ʳ_
infix 3 _⇓_
infix 3 _⇑_

data _⇓ʳ_ : ⊢ T → Result T → Set

-- Convenient aliases.
_⇓_ : ⊢ T → ⊨ T → Set
e ⇓ v = e ⇓ʳ return v

_⇑_ : ⊢ T → Exception → Set
e ⇑ ex = e ⇓ʳ raise ex    
    
data _⇓ʳ_ where
    `_ : (v : ⊨ T)
        → (` v) ⇓ v

    _⊞_
        : e₁ ⇓ n₁
        → e₂ ⇓ n₂
        → (e₁ ⊞ e₂) ⇓ (n₁ + n₂)

    ⊞-exn₁
        : e₁ ⇑ ex
        → (e₁ ⊞ e₂) ⇑ ex

    ⊞-exn₂
        : e₁ ⇓ n₁
        → e₂ ⇑ ex
        → (e₁ ⊞ e₂) ⇑ ex

    test
        : e ⇓ n
        → (test e) ⇓ (test' n)

    test-raise
        : e ⇑ ex
        → (test e) ⇑ ex

    if-then
        : e ⇓ true
        → e₁ ⇓ʳ r
        → (if e then e₁ else e₂) ⇓ʳ r

    if-else
        : e ⇓ false
        → e₂ ⇓ʳ r
        → (if e then e₁ else e₂) ⇓ʳ r

    if-raise
        : e ⇑ ex
        → (if e then e₁ else e₂) ⇑ ex

    throw-rule
        : ∀ {T : Type} → (throw {T = T} ex) ⇑ ex

    try-return
        : ∀ {T : Type} {e : ⊢ T} {v : ⊨ T} {h : Exception → ⊢ T}
        → e ⇓ v
        → (try e catch h) ⇓ v

    try-catch
        : ∀ {T : Type} {e : ⊢ T} {h : Exception → ⊢ T} {r : Result T}
        → e ⇑ ex
        → h ex ⇓ʳ r
        → (try e catch h) ⇓ʳ r
\end{code}

\begin{code}
total : ∀ (e : ⊢ T) → ∃ (λ r → e ⇓ʳ r)
total (` v)      = return v ﹐ ` v
total (throw ex) = raise ex ﹐ throw-rule
total (e₁ ⊞ e₂) with total e₁ | total e₂
... | raise ex  ﹐ p₁  | _               = raise ex ﹐ ⊞-exn₁ p₁
... | return n₁ ﹐ p₁  | raise ex  ﹐ p₂  = raise ex ﹐ ⊞-exn₂ p₁ p₂
... | return n₁ ﹐ p₁  | return n₂ ﹐ p₂  = return (n₁ + n₂) ﹐ (p₁ ⊞ p₂)
total (test e) with total e
... | return n  ﹐ p = return (test' n) ﹐ test p
... | raise ex  ﹐ p = raise ex ﹐ test-raise p
total (if e then e₁ else e₂) with total e
... | return true  ﹐ pe = let (r₁ ﹐ p₁) = total e₁ in r₁ ﹐ if-then pe p₁
... | return false ﹐ pe = let (r₂ ﹐ p₂) = total e₂ in r₂ ﹐ if-else pe p₂
... | raise ex     ﹐ pe = raise ex ﹐ if-raise pe
total (try e catch h) with total e
... | return v  ﹐ p = return v ﹐ try-return p
... | raise ex  ﹐ p = let (r ﹐ q) = total (h ex) in r ﹐ try-catch p q
\end{code}
