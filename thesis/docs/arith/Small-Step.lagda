\begin{code}
module Arith.Small-Step where

open import Arith.Definitions public
open import Data.Nat
open import Data.Bool hiding (T; if_then_else_) renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality.Core using (_≡_) renaming (refl to reflexive)
open import Data.Product using (∃) renaming (_,_ to _﹐_)
\end{code}

\begin{code}

infix 10 _⇾_
data _⇾_ : Γ ⊢ T → Γ ⊢ T → Set where
    ξ-⊞₁ : ∀ {e₁ e₁' e₂ : Γ ⊢ Nat}
        → e₁ ⇾ e₁'
        ----------------------------
        → (e₁ ⊞ e₂) ⇾ (e₁' ⊞ e₂)
    
    ξ-⊞₂ : ∀ {n₁ : ℕ} {e₂ e₂' : Γ ⊢ Nat}
        → e₂ ⇾ e₂'
        ----------------------------
        → (` n₁ ⊞ e₂) ⇾ (` n₁ ⊞ e₂')
    
    β-⊞ : ∀ {n₁ n₂ : ℕ}
        ----------------------------
        → (` n₁ ⊞ ` n₂ ) ⇾ ` (n₁ + n₂)

    ξ-test : ∀ {e e' : Γ ⊢ Nat}
        → e ⇾ e'
        ----------------------------
        → (test e) ⇾ (test e')

    β-test-zero :
        ----------------------------
        test (` 0) ⇾ ` true

    β-test-suc : ∀ {n : ℕ}
        ----------------------------
        → test (` suc n) ⇾ ` false
    
    ξ-if : ∀ {e e' : Γ ⊢ Bool} {e₁ e₂ : Γ ⊢ T}
        → e ⇾ e'
        ----------------------------
        → (if e then e₁ else e₂) ⇾ (if e' then e₁ else e₂)
    
    β-if-then : ∀ {e₁ e₂ : Γ ⊢ T}
        ----------------------------
        → (if ` true then e₁ else e₂) ⇾ e₁
    
    β-if-else : ∀ {e₁ e₂ : Γ ⊢ T}
        ----------------------------
        → (if ` false then e₁ else e₂) ⇾ e₂
\end{code}

β-rules represent actual reduction steps.
ξ-rules represent evaluation under context.

\begin{code}
infix 10 _⇾⃰_

data _⇾⃰_ : Γ ⊢ T → Γ ⊢ T → Set where
    base  : ∀ {e : Γ ⊢ T} → e ⇾⃰ e
    step  : ∀ {e₁ e₂ e₃ : Γ ⊢ T}
        → e₁ ⇾ e₂ 
        → e₂ ⇾⃰ e₃ 
        → e₁ ⇾⃰ e₃

⇾⃰-reflexive : ∀ {e : Γ ⊢ T} → e ⇾⃰ e
⇾⃰-reflexive = base

⇾⃰-transitive : ∀ {e₁ e₂ e₃ : Γ ⊢ T}
    → e₁ ⇾⃰ e₂ 
    → e₂ ⇾⃰ e₃ 
    → e₁ ⇾⃰ e₃
⇾⃰-transitive base q = q
⇾⃰-transitive (step x p) q = step x (⇾⃰-transitive p q)
\end{code}