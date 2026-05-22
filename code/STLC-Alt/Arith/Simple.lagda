\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module STLC.Arith.Simple where

open import Data.Bool renaming (Bool to 𝔹) hiding (T; if_then_else_)
open import Data.Nat renaming (_+_ to infixl 46 _+_)

infixl 146 _⊞₁_ _⊞₂_
infix  120 _else_
infixr  35 _∷_
infix   30 _⊢_↓_ _⊢_↑_

data Type : Set where
    Nat : Type
    Bool : Type

⊨_ : Type → Set
⊨ Nat = ℕ
⊨ Bool = 𝔹


-- open import Context Type public
-- open import Environment Type ⊨_ public

private variable
    T T₁ T₂ T₃ : Type

data ⊢_ : Type → Set where
    `_ : ⊨ T → ⊢ T
    _⊞_ :  ⊢ Nat → ⊢ Nat → ⊢ Nat
    test : ⊢ Nat → ⊢ Bool
    if_then_else_ : ⊢ Bool → ⊢ T → ⊢ T → ⊢ T


data Hole : Set where
    ◌ : Hole

data Frame : Type → Type → Set where
    _else_ : ⊢ T → ⊢ T → Frame T Bool  
    _⊞₁_ : Hole → ⊢ Nat → Frame Nat Nat
    _⊞₂_ : ⊨ Nat → Hole → Frame Nat Nat
    test : Hole → Frame Bool Nat

data Stack (Answer : Type) : Type → Set where 
    []  : Stack Answer Answer
    _∷_ : Stack Answer T₁ → Frame T₁ T₂ → Stack Answer T₂

data Environment : Set where
    δ : Environment

data State (Answer : Type) : Set where
    _⊢_↓_ : (δ : Environment) → Stack Answer T →   ⊨ T → State Answer
    _⊢_↑_ : (δ : Environment) → Stack Answer T →   ⊢ T → State Answer

private variable
    Answer : Type
    s : Stack Answer T

    e e₁ e₂ e₃ : ⊢ T
    v v₁ v₂ : ⊨ T
    n n₁ n₂ : ⊨ Nat

data _∼>_ : State Answer → State Answer → Set where
    step-` : ∀ {v : ⊨ T} → δ ⊢ s ↑ (` v) ∼> δ ⊢ s ↓ v
    step-⊞₁ :       δ ⊢ s ↑ (e₁ ⊞ e₂)    ∼> δ ⊢ s ∷ ◌ ⊞₁ e₂ ↑ e₁
    step-⊞₂ :       δ ⊢ s ∷ ◌ ⊞₁ e₂ ↓ n₁ ∼> δ ⊢ s ∷ n₁ ⊞₂ ◌ ↑ e₂

data _∼>*_ : State Answer → State Answer → Set where
    base : ∀ {s : State Answer} → s ∼>* s
    step : ∀ {s₁ s₂ : State Answer} {s₃}
         → s₁ ∼> s₂
         → s₂ ∼>* s₃
         → s₁ ∼>* s₃

refl : ∀ {s : State Answer} → s ∼>* s
refl = base

trans : ∀ {s₁ s₂ s₃ : State Answer} → s₁ ∼>* s₂ → s₂ ∼>* s₃ → s₁ ∼>* s₃
trans base q = q
trans (step x p) q = step x (trans p q)


_[_] : Stack Answer T → ⊢ T → ⊢ Answer
[] [ e ] = e
(s ∷ e₁ else e₂) [ e ] = s [ if e then e₁ else e₂ ]
(s ∷ ◌ ⊞₁ e₂) [ e ] = s [ e ⊞ e₂ ]
(s ∷ v₁ ⊞₂ ◌) [ e ] = s [ (` v₁) ⊞ e ]
(s ∷ test ◌) [ e ] = s [ test e ] 

expr : State Answer → ⊢ Answer
expr (δ ⊢ s ↓ v) = s [ ` v ]
expr (δ ⊢ s ↑ e) = s [ e ]

data _⇓_ : ⊢ T → ⊨ T → Set where
    `_ : ∀ (v : ⊨ T) →  (` v) ⇓ v
    ADD : e₁ ⇓ n₁ → e₂ ⇓ n₂ → (e₁ ⊞ e₂) ⇓ (n₁ + n₂)
    THEN : {e₂ e₃ : ⊢ T} → e₁ ⇓ true → e₂ ⇓ v → (if e₁ then e₂ else e₃) ⇓ v
    ELSE : {e₂ e₃ : ⊢ T} → e₁ ⇓ false → e₃ ⇓ v → (if e₁ then e₂ else e₃) ⇓ v
    TEST₀ : e ⇓ 0     → (test e) ⇓ true
    TEST₁ : e ⇓ suc n → (test e) ⇓ false 

_⪅_ : ⊢ T → ⊢ T → Set
e₁ ⪅ e₂ = ∀ {v} → e₁ ⇓ v → e₂ ⇓ v

step` : {s s′ : State Answer} → s ∼> s′ → expr s′ ⪅ expr s
step` step-` ev = ev
step` step-⊞₁ ev = ev
step` step-⊞₂ ev = ev

-- ⪅-compositional : {e e′ : ⊢ T} → e ⪅ e′ → ∀ (s : Stack Answer T) → (s [ e ]) ⪅ (s [ e′ ])
-- ⪅-compositional r [] ev = r ev
-- ⪅-compositional r (s ∷ x else x₁) ev = {!   !}
-- ⪅-compositional r (s ∷ x ⊞₁ x₁) ev = {!   !}
-- ⪅-compositional r (s ∷ x ⊞₂ x₁) ev = {!   !}
-- ⪅-compositional r (s ∷ test x) ev = {!   !}

simulateᴿ : ∀ {s s′ : State T} → s ∼>* s′ → expr s′ ⪅ expr s
simulateᴿ (base)      q = q
simulateᴿ (step p ps) q = step` p (simulateᴿ ps q)

correct : ∀ {e : ⊢ T} {v : ⊨ T} → (δ ⊢ [] ↑ e ∼>* δ ⊢ [] ↓ v) → e ⇓ v
correct p = simulateᴿ p (` _)
\end{code}
