\begin{code}
module Arith.Big-Step where

open import Arith.Definitions public
open import Data.Nat
open import Data.Bool hiding (T; if_then_else_) renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality.Core using (_≡_) renaming (refl to reflexive)
open import Data.Product using (∃) renaming (_,_ to _﹐_)
\end{code}

\begin{code}
data _⇓_ : ⊢ T → ⊨ T → Set where
    `_ : (v : ⊨ T) → (` v) ⇓ v
    _⊞_ 
        : e₁ ⇓ n₁
        → e₂ ⇓ n₂
        ----------------------------
        → (e₁ ⊞ e₂) ⇓ (n₁ + n₂)

    test : ∀ {e : ⊢ Nat} {n : ℕ}
        →  e ⇓ n
        ----------------------------
        →  (test e) ⇓ (test' n)
    
    if-then : ∀ {e : ⊢ Bool} {e₁ e₂ : ⊢ T} {v : ⊨ T}
        →  e ⇓ true
        →  e₁ ⇓ v
        ----------------------------
        →  (if e then e₁ else e₂) ⇓ v

    if-else : ∀ {e : ⊢ Bool} {e₁ e₂ : ⊢ T} {v : ⊨ T}
        →  e ⇓ false
        →  e₂ ⇓ v
        ----------------------------
        →  (if e then e₁ else e₂) ⇓ v
\end{code}

\begin{code}

deterministic : ∀ {e : ⊢ T} {v₁ v₂ : ⊨ T}
    → e ⇓ v₁
    → e ⇓ v₂
    → v₁ ≡ v₂
deterministic (` v) (` u) = reflexive

deterministic (p₁ ⊞ p₂) (p₃ ⊞ p₄) with deterministic p₁ p₃ | deterministic p₂ p₄
... | reflexive | reflexive = reflexive

deterministic (test p₁) (test p₂) with deterministic p₁ p₂
... | reflexive = reflexive

deterministic (if-then p₁ p₂) (if-then p₃ p₄) with deterministic p₁ p₃ | deterministic p₂ p₄
... | reflexive | reflexive = reflexive

deterministic (if-then p₁ p₂) (if-else p₃ p₄) with deterministic p₁ p₃ 
... | ()

deterministic (if-else p₁ p₂) (if-then p₃ p₄) with deterministic p₁ p₃ 
... | ()

deterministic (if-else p₁ p₂) (if-else p₃ p₄) with deterministic p₁ p₃ | deterministic p₂ p₄
... | reflexive | reflexive = reflexive


---------------------

total : ∀ (e : ⊢ T)
    → ∃ (λ v → e ⇓ v)
total (` v) = v ﹐ (` v)

total (e₁ ⊞ e₂) with total e₁ | total e₂
... | (n₁ ﹐ p₁) | (n₂ ﹐ p₂) = (n₁ + n₂) ﹐ (p₁ ⊞ p₂)

total (test e) with total e
... | (n ﹐ p) = (test' n) ﹐ (test p)

total (if e then e₁ else e₂) with total e | total e₁ | total e₂
... | false ﹐ p₁ | v₁ ﹐ p₂ | v₂ ﹐ p₃ = v₂ ﹐ if-else p₁ p₃
... | true ﹐ p₁ | v₁ ﹐ p₂ | v₂ ﹐ p₃ = v₁ ﹐ if-then p₁ p₂
\end{code}