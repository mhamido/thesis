\begin{code}
module Arith.Small-Step where

open import Arith.Definitions public
open import Arith.Big-Step public
open import Data.Nat
open import Data.Bool hiding (T; if_then_else_) renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; trans; subst) renaming (refl to reflexive)
open import Data.Product using (∃) renaming (_,_ to _﹐_)
open import Data.Empty using (⊥) renaming (⊥-elim to ex-falso)
import Arith.Denotational as D
\end{code}

\begin{code}

infix 10 _⇾_
data _⇾_ : ⊢ T → ⊢ T → Set where
    ξ-⊞₁ : ∀ {e₁ e₁' e₂ : ⊢ Nat}
        → e₁ ⇾ e₁'
        ----------------------------
        → (e₁ ⊞ e₂) ⇾ (e₁' ⊞ e₂)
    
    ξ-⊞₂ : ∀ {n₁ : ℕ} {e₂ e₂' : ⊢ Nat}
        → e₂ ⇾ e₂'
        ----------------------------
        → (` n₁ ⊞ e₂) ⇾ (` n₁ ⊞ e₂')
    
    β-⊞ : ∀ {n₁ n₂ : ℕ}
        ----------------------------
        → (` n₁ ⊞ ` n₂ ) ⇾ ` (n₁ + n₂)

    ξ-test : ∀ {e e' : ⊢ Nat}
        → e ⇾ e'
        ----------------------------
        → (test e) ⇾ (test e')

    β-test-zero :
        ----------------------------
        test (` 0) ⇾ ` true

    β-test-suc : ∀ {n : ℕ}
        ----------------------------
        → test (` suc n) ⇾ ` false
    
    ξ-if : ∀ {e e' : ⊢ Bool} {e₁ e₂ : ⊢ T}
        → e ⇾ e'
        ----------------------------
        → (if e then e₁ else e₂) ⇾ (if e' then e₁ else e₂)
    
    β-if-then : ∀ {e₁ e₂ : ⊢ T}
        ----------------------------
        → (if ` true then e₁ else e₂) ⇾ e₁
    
    β-if-else : ∀ {e₁ e₂ : ⊢ T}
        ----------------------------
        → (if ` false then e₁ else e₂) ⇾ e₂
\end{code}

β-rules represent actual reduction steps.
ξ-rules represent evaluation under context.

\begin{code}
infix 10 _⇾⃰_

data _⇾⃰_ : ⊢ T → ⊢ T → Set where
    base  : ∀ {e : ⊢ T} → e ⇾⃰ e
    step  : ∀ {e₁ e₂ e₃ : ⊢ T}
        → e₁ ⇾ e₂ 
        → e₂ ⇾⃰ e₃ 
        → e₁ ⇾⃰ e₃

⇾⃰-reflexive : ∀ {e : ⊢ T} → e ⇾⃰ e
⇾⃰-reflexive = base

⇾⃰-transitive : ∀ {e₁ e₂ e₃ : ⊢ T}
    → e₁ ⇾⃰ e₂ 
    → e₂ ⇾⃰ e₃ 
    → e₁ ⇾⃰ e₃
⇾⃰-transitive base q = q
⇾⃰-transitive (step x p) q = step x (⇾⃰-transitive p q)
\end{code}

-- Congruence: lift a multi-step trace through each constructor.
\begin{code}
⇾⃰-⊞₁ : ∀ {e₁ e₁' e₂ : ⊢ Nat} → e₁ ⇾⃰ e₁' → (e₁ ⊞ e₂) ⇾⃰ (e₁' ⊞ e₂)
⇾⃰-⊞₁ base       = base
⇾⃰-⊞₁ (step r p) = step (ξ-⊞₁ r) (⇾⃰-⊞₁ p)

⇾⃰-⊞₂ : ∀ {n : ℕ} {e₂ e₂' : ⊢ Nat} → e₂ ⇾⃰ e₂' → (` n ⊞ e₂) ⇾⃰ (` n ⊞ e₂')
⇾⃰-⊞₂ base       = base
⇾⃰-⊞₂ (step r p) = step (ξ-⊞₂ r) (⇾⃰-⊞₂ p)

⇾⃰-test : ∀ {e e' : ⊢ Nat} → e ⇾⃰ e' → test e ⇾⃰ test e'
⇾⃰-test base       = base
⇾⃰-test (step r p) = step (ξ-test r) (⇾⃰-test p)

⇾⃰-if : ∀ {e e' : ⊢ Bool} {e₁ e₂ : ⊢ T}
    → e ⇾⃰ e' → (if e then e₁ else e₂) ⇾⃰ (if e' then e₁ else e₂)
⇾⃰-if base       = base
⇾⃰-if (step r p) = step (ξ-if r) (⇾⃰-if p)
\end{code}

-- Determinism helpers.
\begin{code}
¬step-` : ∀ {T : Type} {v : ⊨ T} {e' : ⊢ T} → (` v) ⇾ e' → ⊥
¬step-` ()

det : ∀ {T : Type} {e e₁ e₂ : ⊢ T} → e ⇾ e₁ → e ⇾ e₂ → e₁ ≡ e₂
det (ξ-⊞₁ r₁)  (ξ-⊞₁ r₂)   rewrite det r₁ r₂ = reflexive
det (ξ-⊞₂ r₁)  (ξ-⊞₂ r₂)   rewrite det r₁ r₂ = reflexive
det β-⊞         β-⊞          = reflexive
det (ξ-test r₁) (ξ-test r₂)  rewrite det r₁ r₂ = reflexive
det β-test-zero β-test-zero   = reflexive
det β-test-suc  β-test-suc    = reflexive
det (ξ-if r₁)  (ξ-if r₂)    rewrite det r₁ r₂ = reflexive
det β-if-then  β-if-then      = reflexive
det β-if-else  β-if-else      = reflexive

⇾⃰-confluence : ∀ {T : Type} {e e₁ e₂ : ⊢ T}
    → e ⇾⃰ e₁ → e ⇾⃰ e₂
    → (∀ {e' : ⊢ T} → e₁ ⇾ e' → ⊥)
    → (∀ {e' : ⊢ T} → e₂ ⇾ e' → ⊥)
    → e₁ ≡ e₂
⇾⃰-confluence base         base         _   _   = reflexive
⇾⃰-confluence base         (step r _)   ns₁ _   = ex-falso (ns₁ r)
⇾⃰-confluence (step r _)   base         _   ns₂ = ex-falso (ns₂ r)
⇾⃰-confluence (step r₁ p₁) (step r₂ p₂) ns₁ ns₂ rewrite det r₁ r₂ =
    ⇾⃰-confluence p₁ p₂ ns₁ ns₂

`-inj : ∀ {T : Type} {v₁ v₂ : ⊨ T} → _≡_ {A = ⊢ T} (` v₁) (` v₂) → v₁ ≡ v₂
`-inj reflexive = reflexive
\end{code}

-- Simulate: a big-step derivation implies small-step multi-reduction to a value.
\begin{code}
simulate : ∀ {T : Type} {e : ⊢ T} {v : ⊨ T} → e ⇓ v → e ⇾⃰ ` v
simulate (` v)                  = base
simulate (p₁ ⊞ p₂)              =
    ⇾⃰-transitive (⇾⃰-⊞₁ (simulate p₁))
    (⇾⃰-transitive (⇾⃰-⊞₂ (simulate p₂))
    (step β-⊞ base))
simulate (test {n = zero}    p) = 
    ⇾⃰-transitive (⇾⃰-test (simulate p)) 
    (step β-test-zero base)
simulate (test {n = suc _}   p) = 
    ⇾⃰-transitive (⇾⃰-test (simulate p)) 
    (step β-test-suc  base)
simulate (if-then pe p₁)        =
    ⇾⃰-transitive (⇾⃰-if (simulate pe))
    (step β-if-then (simulate p₁))
simulate (if-else pe p₂)        =
    ⇾⃰-transitive (⇾⃰-if (simulate pe))
    (step β-if-else (simulate p₂))

simulateᴿ : ∀ {T : Type} {e : ⊢ T} {v : ⊨ T} → e ⇾⃰ ` v → e ⇓ v
simulateᴿ {e = e} {v = v} tr = 
    let (v' ﹐ p) = total e 
        
        tr' : e ⇾⃰ (` v')
        tr' = simulate p

        eq : (` v') ≡ (` v)
        eq = ⇾⃰-confluence tr' tr ¬step-` ¬step-`
    in subst (e ⇓_) (`-inj eq) p
\end{code}
