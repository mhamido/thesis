Small-step semantics for the arithmetic language with exceptions.
β-rules perform reductions; 
ξ-rules propagate evaluation under context;
exception-propagation rules propagate through the expression tree.

\begin{code}
module Exceptions.Small-Step where

open import Exceptions.Definitions public
open import Exceptions.Big-Step public
open import Data.Nat
open import Data.Bool hiding (T; if_then_else_) renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; subst) renaming (refl to reflexive)
open import Data.Product using (∃) renaming (_,_ to _﹐_)
open import Data.Empty using (⊥) renaming (⊥-elim to ex-falso)
\end{code}

\begin{code}
infix 10 _⇾_

data _⇾_ : ⊢ T → ⊢ T → Set where
    ξ-⊞₁   : e₁ ⇾ e₁'
            → (e₁ ⊞ e₂) ⇾ (e₁' ⊞ e₂)

    ξ-⊞₂   : e₂ ⇾ e₂'
            → (` n₁ ⊞ e₂) ⇾ (` n₁ ⊞ e₂')

    ξ-test  : e ⇾ e'
            → (test e) ⇾ (test e')

    ξ-if    : e ⇾ e'
            → (if e then e₁ else e₂) ⇾ (if e' then e₁ else e₂)

    ξ-try   : e ⇾ e'
            → (try e catch h) ⇾ (try e' catch h)

    β-⊞         : (` n₁ ⊞ ` n₂) ⇾ ` (n₁ + n₂)

    β-test-zero : (test (` 0)) ⇾ ` true

    β-test-suc  : (test (` suc n₁)) ⇾ ` false

    β-if-then   : (if (` true)  then e₁ else e₂) ⇾ e₁

    β-if-else   : (if (` false) then e₁ else e₂) ⇾ e₂

    β-try-ok    : ∀ {T : Type} {v : ⊨ T} {h : Exception → ⊢ T}
                → (try (` v) catch h) ⇾ ` v

    β-try-throw : (try (throw ex) catch h) ⇾ h ex

    -- Exception propagation: throw propagate up through each context.

    β-⊞-exn₁   : (throw ex ⊞ e₂) ⇾ throw ex

    β-⊞-exn₂   : (` n₁ ⊞ throw ex) ⇾ throw ex

    β-test-exn  : (test (throw ex)) ⇾ throw ex

    β-if-exn    : (if throw ex then e₁ else e₂) ⇾ throw ex
\end{code}

Reflexive-transitive closure.

\begin{code}
infix 10 _⇾⃰_

data _⇾⃰_ : ⊢ T → ⊢ T → Set where
    base  : e ⇾⃰ e
    step  : e₁ ⇾ e₂ → e₂ ⇾⃰ e₃ → e₁ ⇾⃰ e₃

⇾⃰-transitive : ∀ {e₁ e₂ e₃ : ⊢ T} → e₁ ⇾⃰ e₂ → e₂ ⇾⃰ e₃ → e₁ ⇾⃰ e₃
⇾⃰-transitive base      q = q
⇾⃰-transitive (step p r) q = step p (⇾⃰-transitive r q)
\end{code}

\begin{code}
⇾⃰-⊞₁ : ∀ {e₁ e₁' e₂ : ⊢ Nat} → e₁ ⇾⃰ e₁' → (e₁ ⊞ e₂) ⇾⃰ (e₁' ⊞ e₂)
⇾⃰-⊞₁ base       = base
⇾⃰-⊞₁ (step r p) = step (ξ-⊞₁ r) (⇾⃰-⊞₁ p)

⇾⃰-⊞₂ : ∀ {n : ℕ} {e₂ e₂' : ⊢ Nat} → e₂ ⇾⃰ e₂' → (` n ⊞ e₂) ⇾⃰ (` n ⊞ e₂')
⇾⃰-⊞₂ base       = base
⇾⃰-⊞₂ (step r p) = step (ξ-⊞₂ r) (⇾⃰-⊞₂ p)

⇾⃰-test : ∀ {e e' : ⊢ Nat} → e ⇾⃰ e' → (test e) ⇾⃰ (test e')
⇾⃰-test base       = base
⇾⃰-test (step r p) = step (ξ-test r) (⇾⃰-test p)

⇾⃰-if : ∀ {e e' : ⊢ Bool} {e₁ e₂ : ⊢ T}
    → e ⇾⃰ e' → (if e then e₁ else e₂) ⇾⃰ (if e' then e₁ else e₂)
⇾⃰-if base       = base
⇾⃰-if (step r p) = step (ξ-if r) (⇾⃰-if p)

⇾⃰-try : ∀ {e e' : ⊢ T} {h : Exception → ⊢ T}
    → e ⇾⃰ e' → (try e catch h) ⇾⃰ (try e' catch h)
⇾⃰-try base       = base
⇾⃰-try (step r p) = step (ξ-try r) (⇾⃰-try p)
\end{code}

\begin{code}
resultExpr : ∀ {T : Type} → Result T → ⊢ T
resultExpr (return v) = ` v
resultExpr (raise ex) = throw ex

¬step-` : ∀ {T : Type} {v : ⊨ T} {e' : ⊢ T} → (` v) ⇾ e' → ⊥
¬step-` ()

¬step-throw : ∀ {T : Type} {ex : Exception} {e' : ⊢ T} → throw ex ⇾ e' → ⊥
¬step-throw ()

¬step-stuck : ∀ {T : Type} {r : Result T} {e' : ⊢ T} → resultExpr r ⇾ e' → ⊥
¬step-stuck {r = return _} = ¬step-`
¬step-stuck {r = raise  _} = ¬step-throw

det : ∀ {T : Type} {e e₁ e₂ : ⊢ T} → e ⇾ e₁ → e ⇾ e₂ → e₁ ≡ e₂
det (ξ-⊞₁ r₁)   (ξ-⊞₁ r₂)   rewrite det r₁ r₂ = reflexive
det (ξ-⊞₂ r₁)   (ξ-⊞₂ r₂)   rewrite det r₁ r₂ = reflexive
det (ξ-test r₁)  (ξ-test r₂)  rewrite det r₁ r₂ = reflexive
det (ξ-if r₁)   (ξ-if r₂)    rewrite det r₁ r₂ = reflexive
det (ξ-try r₁)  (ξ-try r₂)   rewrite det r₁ r₂ = reflexive
det β-⊞          β-⊞          = reflexive
det β-test-zero  β-test-zero  = reflexive
det β-test-suc   β-test-suc   = reflexive
det β-if-then    β-if-then    = reflexive
det β-if-else    β-if-else    = reflexive
det β-try-ok     β-try-ok     = reflexive
det β-try-throw  β-try-throw  = reflexive
det β-⊞-exn₁    β-⊞-exn₁     = reflexive
det β-⊞-exn₂    β-⊞-exn₂     = reflexive
det β-test-exn   β-test-exn   = reflexive
det β-if-exn     β-if-exn     = reflexive

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

resultExpr-inj : ∀ {T : Type} {r₁ r₂ : Result T}
    → resultExpr r₁ ≡ resultExpr r₂ → r₁ ≡ r₂
resultExpr-inj {r₁ = return _} {r₂ = return _} reflexive = reflexive
resultExpr-inj {r₁ = return _} {r₂ = raise  _} ()
resultExpr-inj {r₁ = raise  _} {r₂ = return _} ()
resultExpr-inj {r₁ = raise  _} {r₂ = raise  _} reflexive = reflexive
\end{code}

-- Forward simulation: big-step implies small-step trace to resultExpr r.
\begin{code}
simulate : ∀ {T : Type} {e : ⊢ T} {r : Result T} → e ⇓ʳ r → e ⇾⃰ resultExpr r
simulate (` v)                   = base
simulate (p₁ ⊞ p₂)               =
    ⇾⃰-transitive (⇾⃰-⊞₁ (simulate p₁))
    (⇾⃰-transitive (⇾⃰-⊞₂ (simulate p₂))
    (step β-⊞ base))
simulate (⊞-exn₁ p₁)             =
    ⇾⃰-transitive (⇾⃰-⊞₁ (simulate p₁))
    (step β-⊞-exn₁ base)
simulate (⊞-exn₂ p₁ p₂)          =
    ⇾⃰-transitive (⇾⃰-⊞₁ (simulate p₁))
    (⇾⃰-transitive (⇾⃰-⊞₂ (simulate p₂))
    (step β-⊞-exn₂ base))
simulate (test {n = zero}    p)  =
    ⇾⃰-transitive (⇾⃰-test (simulate p))
    (step β-test-zero base)
simulate (test {n = suc _}   p)  =
    ⇾⃰-transitive (⇾⃰-test (simulate p))
    (step β-test-suc  base)
simulate (test-raise p)           =
    ⇾⃰-transitive (⇾⃰-test (simulate p))
    (step β-test-exn base)
simulate (if-then pe p₁)          =
    ⇾⃰-transitive (⇾⃰-if (simulate pe))
    (step β-if-then (simulate p₁))
simulate (if-else pe p₂)          =
    ⇾⃰-transitive (⇾⃰-if (simulate pe))
    (step β-if-else (simulate p₂))
simulate (if-raise pe)            =
    ⇾⃰-transitive (⇾⃰-if (simulate pe))
    (step β-if-exn base)
simulate throw-rule               = base
simulate (try-return p)           =
    ⇾⃰-transitive (⇾⃰-try (simulate p))
    (step β-try-ok base)
simulate (try-catch p q)          =
    ⇾⃰-transitive (⇾⃰-try (simulate p))
    (step β-try-throw (simulate q))

-- Reverse simulation: small-step trace to resultExpr r implies big-step.
simulateᴿ : ∀ {T : Type} {e : ⊢ T} {r : Result T} → e ⇾⃰ resultExpr r → e ⇓ʳ r
simulateᴿ {e = e} {r = r} tr =
    let (r' ﹐ p) = total e

        tr'       : e ⇾⃰ resultExpr r'
        tr'       = simulate p

        eq        : resultExpr r' ≡ resultExpr r
        eq        = ⇾⃰-confluence tr' tr ¬step-stuck ¬step-stuck
    in subst (e ⇓ʳ_) (resultExpr-inj eq) p
\end{code}
