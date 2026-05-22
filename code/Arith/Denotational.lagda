\begin{code}
module Arith.Denotational where

open import Arith.Definitions public
open import Data.Nat
open import Data.Bool hiding (T; if_then_else_) renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality.Core using (_≡_) renaming (refl to reflexive)
open import Data.Product using (∃) renaming (_,_ to _﹐_)
\end{code}

\begin{code}
⟦_⟧ : ∀ {T} → ⊢ T → ⊨ T
⟦ ` v ⟧ = v
⟦ e₁ ⊞ e₂ ⟧ = ⟦ e₁ ⟧ + ⟦ e₂ ⟧
⟦ test e ⟧ = test' (⟦ e ⟧)
⟦ if e then e₁ else e₂ ⟧ with ⟦ e ⟧
... | true = ⟦ e₁ ⟧
... | false = ⟦ e₂ ⟧


open import Arith.Big-Step public

simulate : ∀ {T : Type} {e : ⊢ T} {v : ⊨ T} → e ⇓ v → ⟦ e ⟧ ≡ v
simulate (` v) = reflexive
simulate (e₁ ⊞ e₂) rewrite simulate e₁ | simulate e₂ = reflexive
simulate (test e) rewrite simulate e = reflexive
simulate (if-then e₁ e₂) rewrite simulate e₁ | simulate e₂ = reflexive
simulate (if-else e₁ e₂) rewrite simulate e₁ | simulate e₂ = reflexive

simulateᴿ : ∀ {T : Type} (e : ⊢ T) {v : ⊨ T} → ⟦ e ⟧ ≡ v → e ⇓ v

simulateᴿ (` x) reflexive = ` x
simulateᴿ (e₁ ⊞ e₂) p with ⟦ e₁ ⟧ in eq₁ | ⟦ e₂ ⟧ in eq₂ | p
... | v₁ | v₂ | reflexive = simulateᴿ e₁ eq₁ ⊞ simulateᴿ e₂ eq₂

simulateᴿ (test e) p with ⟦ e ⟧ in eq | p
... | v | reflexive = test (simulateᴿ e eq)

simulateᴿ (if e then e₁ else e₂) p with ⟦ e ⟧ in eq | p
... | true  | reflexive = if-then (simulateᴿ e eq) (simulateᴿ e₁ reflexive)
... | false | reflexive = if-else (simulateᴿ e eq) (simulateᴿ e₂ reflexive)
\end{code}