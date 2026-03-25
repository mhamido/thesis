\begin{code}
module Arith.Denotational where

open import Arith.Definitions public
open import Data.Nat
open import Data.Bool hiding (T; if_then_else_) renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality.Core using (_≡_) renaming (refl to reflexive)
open import Data.Product using (∃) renaming (_,_ to _﹐_)
\end{code}

\begin{code}
_⟦_⟧ : ∀ {Γ T} → Environment Γ → Γ ⊢ T → ⊨ T
δ ⟦ ` v ⟧ = v
δ ⟦ e₁ ⊞ e₂ ⟧ = δ ⟦ e₁ ⟧ + δ ⟦ e₂ ⟧
δ ⟦ test e ⟧ = test' (δ ⟦ e ⟧)
δ ⟦ if e then e₁ else e₂ ⟧ with δ ⟦ e ⟧
... | true = δ ⟦ e₁ ⟧
... | false = δ ⟦ e₂ ⟧
\end{code}