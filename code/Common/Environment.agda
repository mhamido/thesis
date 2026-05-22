{-# OPTIONS --safe #-}
module Common.Environment (Type : Set) (Value : Type → Set) where

open import Common.Context (Type)

private variable
  Γ : Context
  T : Type

data Environment : Context → Set where
  ∅     : Environment ∅
  _,_   : Environment Γ
        → Value T
        --------------------
        → Environment (Γ , T)

⊨
lookupₑ : Environment Γ → T ∈ Γ → Value T
lookupₑ (γ , x) Z = x
lookupₑ (γ , x) (S y) = lookupₑ γ y


