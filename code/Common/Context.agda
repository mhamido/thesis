{-# OPTIONS --safe #-}

module Common.Context (Type : Set) where
open import Data.Bool using (_∧_; true; false) renaming (Bool to 𝔹)
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n) renaming (_<_ to _≺_; _≤?_ to _≼?_; _+_ to _N+_)
infixl 5 _,_

data Context : Set where
  ∅    : Context
  _,_  : Context → Type → Context

private variable
  Γ Δ     : Context
  T T₁ T₂ : Type

data _∈_ : Type → Context → Set where
  Z   : T ∈ (Γ , T)
  S_  : T₁ ∈ Γ → T₁ ∈ (Γ , T₂)

length : Context → ℕ
length ∅ = zero
length (Γ , _) = suc (length Γ )

lookup : {Γ : Context} → {n : ℕ} → (p : n ≺ (length Γ)) → Type
lookup {Γ , A} {zero} (s≤s z≤n) = A
lookup {Γ , A} {suc n} (s≤s p) = lookup p

𝟘 : {T : Type} {δ : Context} → T ∈ (δ , T)
𝟘 = Z

𝟙 : {T₁ T₂ : Type} {δ : Context} → T₁ ∈ (δ , T₁ , T₂)
𝟙 = S 𝟘

𝟚 : {T₁ T₂ T₃ : Type} {δ : Context} → T₁ ∈ (δ , T₁ , T₂ , T₃)
𝟚 = S 𝟙

𝟛 : {T₁ T₂ T₃ T₄ : Type} {δ : Context} → T₁ ∈ (δ , T₁ , T₂ , T₃ , T₄)
𝟛 = S 𝟚