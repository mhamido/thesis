\begin{code}
module STLC.Big-Step where

open import STLC.Definitions public

record Closure (A B : Type) : Set

⊨_ : Type → Set
⊨ Bool = 𝔹
⊨ Nat  = ℕ
⊨ (A ⇒ B) = Closure A B

open import Common.Environment Type ⊨_ public

record Closure A B where
  inductive 
  constructor ⟨_,_⟩
  field
    {Γᶜ} : Context
    δᶜ : Environment Γᶜ
    eᶜ : (Γᶜ , A) ⊢ B

private variable
  Δ Γᶜ : Context
  δ : Environment Γ
  δᶜ : Environment Γᶜ
  eᶜ : (Γᶜ , T₁) ⊢ T₂
  e e₀ e₁ e₂ e₃ : Γ ⊢ T
  v v₁ v₂ v₃ : ⊨ T

data _⊢_⇓_ : Environment Γ → Γ ⊢ T → ⊨ T → Set where
  NAT : (n : ℕ) → δ ⊢ Nat n ⇓ n
  BOOL : (b : 𝔹) → δ ⊢ Bool b ⇓ b

  VAR : ∀ {Γ} {δ : Environment Γ} → 
        (x : T ∈ Γ) → δ ⊢ Var x ⇓ (lookupₑ δ x)

  ABS : ∀ {Γ} {δ : Environment Γ} → 
        (e : (Γ , T₁) ⊢ T₂) → 
        δ ⊢ ƛ e ⇓ ⟨ δ , e ⟩

  _⊞_ 
    : δ ⊢ e₁ ⇓ v₁
    → δ ⊢ e₂ ⇓ v₂
    ----------------------------
    → δ ⊢ e₁ ⊞ e₂ ⇓ (v₁ + v₂)

  if-true
    : {e₁ : Γ ⊢ T} {v : ⊨ T}
    → δ ⊢ e ⇓ true
    → δ ⊢ e₁ ⇓ v
    ----------------------------
    → δ ⊢ if e then e₁ else e₂ ⇓ v

  if-false
    : {e₂ : Γ ⊢ T} {v : ⊨ T}
    → δ ⊢ e ⇓ false
    → δ ⊢ e₂ ⇓ v
    ----------------------------
    → δ ⊢ if e then e₁ else e₂ ⇓ v

  app 
    : ∀ {e₀ : Γ ⊢ (T₁ ⇒ T₂)} {e₁ : Γ ⊢ T₁} {v : ⊨ T₂}
    → δ ⊢ e₀ ⇓ ⟨ δᶜ , eᶜ ⟩
    → δ ⊢ e₁ ⇓ v₁
    → (δᶜ , v₁) ⊢ eᶜ ⇓ v
    ----------------------------
    → δ ⊢ e₀ · e₁ ⇓ v

open import Data.Product using (Σ; ∃) renaming (_,_ to _ʻ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

{-# TERMINATING #-}
total : ∀ {Γ} {δ : Environment Γ} (e : Γ ⊢ T) → 
        ∃ (λ v → δ ⊢ e ⇓ v)
total (Nat x) = x ʻ NAT x
total (Bool x) = x ʻ BOOL x
total (e₁ ⊞ e₂) with total e₁ | total e₂
... | (v₁ ʻ p) | (v₂ ʻ q) = (v₁ + v₂) ʻ _⊞_ p q

total (if e then e₁ else e₂) with total e | total e₁ | total e₂
... | (true  ʻ p) | (v ʻ q) | _ = v ʻ if-true p q
... | (false ʻ p) | _ | (v ʻ q) = v ʻ if-false p q

total {δ = δ} (Var x) = lookupₑ δ x ʻ VAR x
total (ƛ e) = ⟨ _ , e ⟩ ʻ ABS e
total (e₁ · e₂) with total e₁ | total e₂
... | (⟨ δᶜ , eᶜ ⟩ ʻ p) | (v₂ ʻ q) with total {δ = δᶜ , v₂} eᶜ 
... | (v ʻ r) = v ʻ app p q r

deterministic : ∀ {Γ} {δ : Environment Γ} {e : Γ ⊢ T} {v₁ v₂ : ⊨ T} 
            → δ ⊢ e ⇓ v₁ 
            → δ ⊢ e ⇓ v₂ 
            → v₁ ≡ v₂
deterministic (NAT _) (NAT _) = refl
deterministic (BOOL _) (BOOL _) = refl
deterministic (VAR _) (VAR _) = refl
deterministic (ABS _) (ABS _) = refl

deterministic (p1 ⊞ p2) (p3 ⊞ p4) with deterministic p1 p3 | deterministic p2 p4
... | refl | refl = refl

deterministic (if-true p1 p2) (if-true p3 p4) with deterministic p1 p3 | deterministic p2 p4
... | refl | refl = refl

deterministic (if-true p1 p2) (if-false p3 p4) with deterministic p1 p3
... | ()
deterministic (if-false p1 p2) (if-true p3 p4) with deterministic p1 p3
... | ()

deterministic (if-false p1 p2) (if-false p3 p4) with deterministic p1 p3 | deterministic p2 p4
... | refl | refl = refl

deterministic (app p1 p2 p3) (app p4 p5 p6) with deterministic p1 p4 | deterministic p2 p5
... | refl | refl = deterministic p3 p6 


