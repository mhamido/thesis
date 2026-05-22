\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module STLC.Arith.StuckTypes where

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


open import Context Type public
open import Environment Type ⊨_ public

private variable
    T T₁ T₂ T₃ : Type
    Γ Δ : Context
    δ : Environment Γ

data _⊢_ : Context → Type → Set where
    `_ : ⊨ T → Γ ⊢ T
    Var : T ∈ Γ → Γ ⊢ T
    _⊞_ :  Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Nat
    test : Γ ⊢ Nat → Γ ⊢ Bool
    Let_In_ : Γ ⊢ T₁ → (Γ , T₁) ⊢ T₂ → Γ ⊢ T₂
    if_then_else_ : Γ ⊢ Bool → Γ ⊢ T → Γ ⊢ T → Γ ⊢ T


data Hole : Set where
    ◌ : Hole

data Frame : Type → Type → Set where
    _else_ : Γ ⊢ T → Γ ⊢ T → Frame T Bool  
    _⊞₁_ : Hole → Γ ⊢ Nat → Frame Nat Nat
    _⊞₂_ : ⊨ Nat → Hole → Frame Nat Nat
    test : Hole → Frame Bool Nat
    Let₁_In : Hole → (Γ , T₁) ⊢ T₂ → Frame T₂ T₁
    Let₂_In : ⊨ T₁ → Hole          → Frame T₂ T₂


data Stack (Answer : Type) : Type → Set where 
    []  : Stack Answer Answer
    _∷_ : Stack Answer T₁ → Frame T₁ T₂ → Stack Answer T₂

data State (Answer : Type) : Set where
    _⊢_↓_ : (δ : Environment Γ) → Stack Answer T →   ⊨ T → State Answer
    _⊢_↑_ : (δ : Environment Γ) → Stack Answer T → Γ ⊢ T → State Answer

private variable
    Answer : Type
    s : Stack Answer T

    e e₁ e₂ e₃ : Γ ⊢ T
    v v₁ v₂ : ⊨ T
    n n₁ n₂ : ⊨ Nat

data _∼>_ : State Answer → State Answer → Set where
    step-` : ∀ {v : ⊨ T} → δ ⊢ s ↑ (` v) ∼> δ ⊢ s ↓ v
    step-var : ∀ {x : T ∈ Γ} → δ ⊢ s ↑ Var x ∼> δ ⊢ s ↓ lookupₑ δ x
    step-⊞₁ :       δ ⊢ s ↑ (e₁ ⊞ e₂)    ∼> δ ⊢ s ∷ ◌ ⊞₁ e₂ ↑ e₁
    step-⊞₂ :       δ ⊢ s ∷ ◌ ⊞₁ e₂ ↓ n₁ ∼> δ ⊢ s ∷ n₁ ⊞₂ ◌ ↑ e₂
    step-let₁ : δ ⊢ s ↑ (Let e₁ In e₂) ∼> δ ⊢ (s ∷ (Let₁ ◌ In e₂)) ↑ e₁
    step-let₂ : 
        {v₁ : ⊨ T₁} →
        (δ ⊢ s ∷ (Let₁ ◌ In e₂) ↓ v₁) ∼> (δ ⊢ s ∷ (Let₂ v₁ In ◌) ↑ e₂)

_[_] : {Γ : Context} → Stack Answer T → Γ ⊢ T → Γ ⊢ Answer
[] [ e ] = e
(s ∷ e₁ else e₂) [ e ] = s [ if e then {!   !} else {!   !} ]
(s ∷ ◌ ⊞₁ x₁) [ e ] = s [ e ⊞ {!   !} ]
(s ∷ x ⊞₂ ◌) [ e ] = s [ (` x) ⊞ e ]
(s ∷ test ◌) [ e ] = s [ test e ]
(s ∷ Let₁ ◌ In x₁) [ e ] = s [ (Let e In {!   !}) ]
(s ∷ Let₂ x In ◌) [ e ] = s [ Let ` x In {!  e !} ] 
-- e : Γ ⊢ T, but we need to slot it into a position where (Γ , T₁) ⊢ T is expected!


-- data apply_[_]≡_ : Stack Answer T → Δ ⊢ T → Γ ⊢ Answer → Set where
--     base : apply [] [ e ]≡ e
    
--     else : apply s [ if e then e₁ else e₂ ]≡ e₃
--          → apply (s ∷ e₁ else e₂) [ e ]≡ e₃
    
--     add₁ : apply s [ e ⊞ e₂ ]≡ e₃
--          → apply (s ∷ ◌ ⊞₁ e₂) [ e ]≡ e₃

--     add₂ : apply s [ (` n) ⊞ e ]≡ e₃
--          → apply (s ∷ n ⊞₂ ◌) [ e ]≡ e₃

--     tst : apply s [ test e ]≡ e₃
--         → apply (s ∷ test ◌) [ e ]≡ e₃

--     let₁ : apply s [ Let e₁ In e₂ ]≡ e₃
--          → apply (s ∷ Let₁ ◌ In e₂) [ e₁ ]≡ e₃

--     let₂ : ∀ {e₂ : (Γ , T₁) ⊢ T₂} {v₁ : ⊨ T₁}
--          → apply s [ Let (` v₁) In e₂ ]≡ e₃
--          → apply (s ∷ Let₂ v₁ In ◌) [ e₂ ]≡ e₃



expr : State Answer → Γ ⊢ Answer
-- expr (_ ⊢ s ↓ v) = s [ ` v ]
-- expr (_ ⊢ s ↑ e) = s [ e ]

data _⇓_ : Γ ⊢ T → ⊨ T → Set where
    VAL : ∀ {v : ⊨ T} →  (` v) ⇓ v
    ADD : e₁ ⇓ n₁ → e₂ ⇓ n₂ → (e₁ ⊞ e₂) ⇓ (n₁ + n₂)
    THEN : {e₂ e₃ : Γ ⊢ T} → e₁ ⇓ true → e₂ ⇓ v → (if e₁ then e₂ else e₃) ⇓ v
    ELSE : {e₂ e₃ : Γ ⊢ T} → e₁ ⇓ false → e₃ ⇓ v → (if e₁ then e₂ else e₃) ⇓ v
    TEST₀ : e ⇓ 0     → (test e) ⇓ true
    TEST₁ : e ⇓ suc n → (test e) ⇓ false 

_≤ₑ_ : Γ ⊢ T → Γ ⊢ T → Set
e₁ ≤ₑ e₂ = ∀ {v} → e₁ ⇓ v → e₂ ⇓ v

step : {s s′ : State Answer} → s ∼> s′ → expr s ≤ₑ expr s′
-- step step-` v = v
-- step step-⊞₁ v = v
-- step step-⊞₂ v = v



\end{code}
