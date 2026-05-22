\begin{code}
module Exceptions.Denotational where

open import Exceptions.Definitions public
open import Data.Nat
open import Data.Bool hiding (T; if_then_else_) renaming (Bool to
    𝔹)
open import Data.Product using (∃) renaming (_,_ to _﹐_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
\end{code}

The denotational semantics for the arithmetic language with exceptions.
\begin{code}
open import Exceptions.Big-Step public

interpret : ∀ {T : Type} → (⊢ T) → Result T
interpret {T} (` x) = return x

interpret (t₁ ⊞ t₂) with interpret t₁ | interpret t₂
... | raise ex  | _      = raise ex
... | return _  | raise ex = raise ex
... | return n₁ | return n₂  = return (n₁ + n₂)

interpret (test t) with interpret t 
... | return zero = return true
... | return (suc x) = return false
... | raise x = raise x

interpret (if t then t₁ else t₂) with interpret t
... | return true = interpret t₁
... | return false = interpret t₂
... | raise x = raise x

interpret (throw x) = raise x
interpret (try t catch x) with interpret t
... | raise ex = interpret (x ex)
... | return v = return v
\end{code}

\begin{code}
simulate : ∀ {T : Type} {e : ⊢ T} {r : Result T} → e ⇓ʳ r → interpret e ≡ r
simulate {Nat} (` v) = refl
simulate {Bool} (` v) = refl
simulate (throw-rule {ex}) = refl
simulate (t₁ ⊞ t₂)       rewrite simulate t₁ | simulate t₂ = refl
simulate (⊞-exn₁ t₁)     rewrite simulate t₁               = refl
simulate (⊞-exn₂ t₁ t₂)  rewrite simulate t₁ | simulate t₂ = refl
simulate (test {n = zero}  t) rewrite simulate t = refl
simulate (test {n = suc _} t) rewrite simulate t = refl
simulate (test-raise t)   rewrite simulate t = refl
simulate (if-then t e)    rewrite simulate t = simulate e
simulate (if-else t e)    rewrite simulate t = simulate e
simulate (if-raise t)     rewrite simulate t = refl
simulate (try-return x)   rewrite simulate x = refl
simulate (try-catch x d)  rewrite simulate x = simulate d

simulateᴿ : ∀ {T : Type} (e : ⊢ T) {r : Result T} → interpret e ≡ r → e ⇓ʳ r
simulateᴿ (` x)     refl = ` x
simulateᴿ (throw x)  refl = throw-rule
simulateᴿ (t₁ ⊞ t₂) p with interpret t₁ in eq₁ | interpret t₂ in eq₂ | p
... | raise ex  | _          | refl = ⊞-exn₁ (simulateᴿ t₁ eq₁)
... | return n₁ | raise ex   | refl = ⊞-exn₂ (simulateᴿ t₁ eq₁) (simulateᴿ t₂ eq₂)
... | return n₁ | return n₂  | refl = simulateᴿ t₁ eq₁ ⊞ simulateᴿ t₂ eq₂

simulateᴿ (test t) p with interpret t in eq | p
... | raise ex       | refl = test-raise (simulateᴿ t eq)
... | return zero    | refl = test (simulateᴿ t eq)
... | return (suc n) | refl = test (simulateᴿ t eq)

simulateᴿ (if c then t₁ else t₂) p with interpret c in eq | p
... | raise ex     | refl = if-raise (simulateᴿ c eq)
... | return true  | p′   = if-then (simulateᴿ c eq) (simulateᴿ t₁ p′)
... | return false | p′   = if-else (simulateᴿ c eq) (simulateᴿ t₂ p′)

simulateᴿ (try t catch h) p with interpret t in eq | p
... | raise ex | p′   = try-catch (simulateᴿ t eq) (simulateᴿ (h ex) p′)
... | return v | refl = try-return (simulateᴿ t eq)