\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module STLC.Arith.WithLetBindings where

open import Data.Bool renaming (Bool to 𝔹) hiding (T; if_then_else_)
open import Data.Nat renaming (_+_ to infixl 46 _+_)
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to _،_)

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
    T T₁ T₂ T₃ Answer : Type
    Γ Δ Δ′ : Context
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

data Frame : Context → Context → Type → Type → Set where
    _else_ : Γ ⊢ T → Γ ⊢ T → Frame Γ Γ T Bool  
    _⊞₁_ : Hole → Γ ⊢ Nat → Frame Γ Γ Nat Nat
    _⊞₂_ : ⊨ Nat → Hole → Frame Γ Γ Nat Nat
    test : Hole → Frame Γ Γ Bool Nat
    Let₁_In : Hole → (Γ , T₁) ⊢ T₂ → Frame Γ Γ T₂ T₁
    Let₂_In : ⊨ T₁ → Hole → Frame Γ (Γ , T₁) T₂ T₂
\end{code}

An element of type Frame Γ Δ A B is an "expression node" of type ⊢ A with a
hole of type Δ ⊢ B. It represents a computation in context Γ, (possibly waiting for a value of type B computed in context Δ) to produce a value of type A.
Note that most frames don't change context (Γ = Δ), but app₃ does.

What each type parameter of `Stack Answer Γ Δ T` means:
  - The base context (prior to any extension) is Γ.
  - The current hole context is Δ
  - The hole is in the place of a term of type T.

\begin{code}
data Stack (Answer : Type) : Context → Context → Type → Set where
  []  : Stack Answer Γ Γ Answer 
  _∷_ : Stack Answer Γ Δ T₁ → Frame Δ Δ′ T₁ T₂ → Stack Answer Γ Δ′ T₂

data State : Context → Type → Set where
  -- Δ is the current context, δ is its environment
  -- Γ is the base context (answer context)
  _⊢_↓_ : (δ : Environment Δ) → Stack Answer Γ Δ T → ⊨ T → State Γ Answer
  _⊢_↑_ : (δ : Environment Δ) → Stack Answer Γ Δ T → Δ ⊢ T → State Γ Answer

private variable
    e e₁ e₂ e₃ : Γ ⊢ T
    v v₁ v₂ : ⊨ T
    n n₁ n₂ : ⊨ Nat

_[_] : Stack Answer Γ Δ T → Δ ⊢ T → Γ ⊢ Answer
[] [ e ] = e
(s ∷ e₁ else e₂) [ e ] = s [ if e then e₁ else e₂ ]
(s ∷ ◌ ⊞₁ x₁) [ e ] = s [ e ⊞ x₁ ]
(s ∷ x ⊞₂ ◌) [ e ] = s [ (` x) ⊞ e ]
(s ∷ test ◌) [ e ] = s [ test e ]
(s ∷ Let₁ ◌ In x₁) [ e ] = s [ Let e In x₁ ]
(s ∷ Let₂ x In ◌) [ e ] = s [ Let ` x In e ]

expr : State Γ Answer → Γ ⊢ Answer
expr (δ ⊢ s ↓ v) = s [ ` v ]
expr (δ ⊢ s ↑ e) = s [ e ]

-- module Example-Let where
--   e₀ : ∅ ⊢ Nat
--   e₀ = Let (` 1) In (Var Z)

--   -- Step 0: Initial state
--   s₀ : State Nat
--   s₀ = ∅ ⊢ [] ↑ (Let (` 1) In (Var Z))
--   _ = {! expr s₀  !}

--   -- expr s₀ = (∅ ، Let (` 1) In (Var Z))
  
--   s₁ : State Nat
--   s₁ = ∅ ⊢ ([] ∷ (Let₁ ◌ In (Var Z))) ↑ (` 1)
--   _ = {! expr s₁  !}
  
--   s₂ : State Nat
--   s₂ = ∅ ⊢ ([] ∷ Let₁ ◌ In (Var Z)) ↓ 1
--   _ = {! expr s₂ !}

--   -- expr s₂ = (∅ ، Let ` 1 In (Var Z))
  
--   s₃ : State Nat
--   s₃ = (∅ , 1) ⊢ ([] ∷ Let₂ 1 In ◌) ↑ Var Z
--   _ = {! expr s₃  !}

--   -- expr s₃ = (∅ ، Let ` 1 In Var Z)
--   -- Note: Environment is (∅ , Nat) but gives us expression in ∅.
  
--   s₄ : State Nat
--   s₄ = (∅ , 1) ⊢ ([] ∷ (Let₂ 1 In ◌)) ↓ 1
--   _ = {! expr s₄  !}

--   -- expr s₄ = (∅ ، Let ` 1 In ` 1)
  
--   s₅ : State Nat
--   s₅ = ∅ ⊢ [] ↓ 1
--   _ = {! expr s₅  !}

\end{code}

At every step, `expr` returns an expression in the context ∅, even though the environment changes from ∅ to (∅ , Nat) and back.

\begin{code}
private variable
    s : Stack Answer Γ Δ T

data _∼>_ : State Γ Answer → State Γ Answer → Set where
    step-` : ∀ {v : ⊨ T} → δ ⊢ s ↑ (` v) ∼> δ ⊢ s ↓ v
    step-⊞₁ :       δ ⊢ s ↑ (e₁ ⊞ e₂)    ∼> δ ⊢ s ∷ ◌ ⊞₁ e₂ ↑ e₁
    step-⊞₂ :       δ ⊢ s ∷ ◌ ⊞₁ e₂ ↓ n₁ ∼> δ ⊢ s ∷ n₁ ⊞₂ ◌ ↑ e₂
    step-let : δ ⊢ s ↑ (Let e₁ In e₂) ∼> δ ⊢ s ∷ (Let₁ ◌ In e₂) ↑ e₁
    step-let₁ : {v₁ : ⊨ T₁} {e₂ : (Γ , T₁) ⊢ T₂}
        → δ ⊢ s ∷ (Let₁ ◌ In e₂) ↓ v₁ ∼> (δ , v₁) ⊢ s ∷ (Let₂ v₁ In ◌) ↑ e₂
    step-let₂ : {v₁ : ⊨ T₁} {v₂ : ⊨ T₂}
        → (δ , v₁) ⊢ s ∷ (Let₂ v₁ In ◌) ↓ v₂ ∼> δ ⊢ s ↓ v₂

data _∼>*_ : State Γ Answer → State Γ Answer → Set where
    base : ∀ {s : State Γ Answer} → s ∼>* s
    step : ∀ {s₁ s₂ : State Γ Answer} {s₃}
         → s₁ ∼> s₂
         → s₂ ∼>* s₃
         → s₁ ∼>* s₃

\end{code}

\begin{code}
data _⊢_⇓_ : Environment Γ → Γ ⊢ T → ⊨ T → Set where
    -- `_ : ∀ (v : ⊨ T) → (` v) ⇓ v
    `_ : ∀ {Γ} {δ : Environment Γ} (v : ⊨ T) 
        → δ ⊢ (` v) ⇓ v
    ADD : {e₁ e₂ : Γ ⊢ Nat}
        → δ ⊢ e₁ ⇓ n₁ 
        → δ ⊢ e₂ ⇓ n₂ 
        --------------------------
        → δ ⊢ (e₁ ⊞ e₂) ⇓ (n₁ + n₂)
    THEN : {e₂ e₃ : Γ ⊢ T} → δ ⊢ e₁ ⇓ true → δ ⊢ e₂ ⇓ v 
        → δ ⊢ (if e₁ then e₂ else e₃) ⇓ v
    ELSE : {e₂ e₃ : Γ ⊢ T} → δ ⊢ e₁ ⇓ false → δ ⊢ e₃ ⇓ v 
        → δ ⊢ (if e₁ then e₂ else e₃) ⇓ v
    
    TEST₀ : δ ⊢ e ⇓ 0     
        → δ ⊢ (test e) ⇓ true
    TEST₁ : δ ⊢ e ⇓ suc n 
        → δ ⊢ (test e) ⇓ false 
    
    LET : {e₁ : Γ ⊢ T₁} {v₁ : ⊨ T₁} {v₂ : ⊨ T₂}
        → δ ⊢ e₁ ⇓ v₁
        → (δ , v₁) ⊢ e₂ ⇓ v₂
        ----------------
        → δ ⊢ (Let e₁ In e₂) ⇓ v₂

_⪅_ : Γ ⊢ T → Γ ⊢ T → Set
e₁ ⪅ e₂ = ∀ {δ v} → δ ⊢ e₁ ⇓ v → δ ⊢ e₂ ⇓ v

test-ctx
    : {e e′ : Γ ⊢ Nat}
    → e ⪅ e′ → test e ⪅ test e′
test-ctx r (TEST₀ p) = TEST₀ (r p)
test-ctx r (TEST₁ p) = TEST₁ (r p)

plus-ctx₁
    : {e e′ e₁ : Γ ⊢ Nat}
    → e ⪅ e′ → (e ⊞ e₁) ⪅ (e′ ⊞ e₁)
plus-ctx₁ r (ADD p₁ p₂) = ADD (r p₁) p₂

plus-ctx₂
    : {e e′ : Γ ⊢ Nat} {n₀ : ℕ}
    → e ⪅ e′ → ((` n₀) ⊞ e) ⪅ ((` n₀) ⊞ e′)
plus-ctx₂ r (ADD p₁ p₂) = ADD p₁ (r p₂)

if-ctx
    : {e e′ : Γ ⊢ Bool} {e₁ e₂ : Γ ⊢ T} 
    → e ⪅ e′ → (if e then e₁ else e₂) ⪅ (if e′ then e₁ else e₂)
if-ctx r (THEN p₁ p₂) = THEN (r p₁) p₂
if-ctx r (ELSE p₁ p₂) = ELSE (r p₁) p₂ 

Let-ctx₁ 
    : {e e′ : Γ ⊢ T₁}
    → e ⪅ e′ → (Let e In e₂) ⪅ (Let e′ In e₂)
Let-ctx₁ r (LET p₁ p₂) = LET (r p₁) p₂

Let-ctx₂ 
    : {v₁ : ⊨ T₁} {e e′ : (Γ , T₁) ⊢ T₂}
    → e ⪅ e′ → (Let ` v₁ In e) ⪅ (Let ` v₁ In e′)
Let-ctx₂ r (LET p₁ p₂) = LET p₁ (r p₂)

the : (T : Set) → T → T
the _ x = x

Let-refine : {v₁ : ⊨ T₁} {v₂ : ⊨ T₂}
    → (` v₂) ⪅ the (Γ ⊢ T₂) (Let ` v₁ In ` v₂)
Let-refine (` v) = LET (` _) (` v)

⪅-compositional 
    : ∀ {Γ Δ : Context} {A : Type} {e e′ : Δ ⊢ A} 
    → e ⪅ e′ 
    → ∀ (s : Stack Answer Γ Δ A) 
    → (s [ e ]) ⪅ (s [ e′ ])
⪅-compositional r [] = r
⪅-compositional r (s ∷ e₁ else e₂) = ⪅-compositional (if-ctx r) s
⪅-compositional r (s ∷ ◌ ⊞₁ e₂) = ⪅-compositional (plus-ctx₁ r) s
⪅-compositional r (s ∷ v₁ ⊞₂ ◌) = ⪅-compositional (plus-ctx₂ r) s
⪅-compositional r (s ∷ test ◌) = ⪅-compositional (test-ctx r) s
⪅-compositional r (s ∷ Let₁ ◌ In e₂) = ⪅-compositional (Let-ctx₁ r) s
⪅-compositional r (s ∷ Let₂ v₁ In ◌) = ⪅-compositional (Let-ctx₂ r) s

step` : {s s′ : State Γ Answer} → s ∼> s′ → expr s′ ⪅ expr s
step` step-` ev = ev
step` step-⊞₁ ev = ev 
step` step-⊞₂ ev = ev
step` step-let ev = ev
step` step-let₁ ev = ev
step` (step-let₂ {s = s}) ev = ⪅-compositional Let-refine s ev

simulateᴿ : ∀ {s s′ : State Γ T} → s ∼>* s′ → expr s′ ⪅ expr s
simulateᴿ (base)      q = q
simulateᴿ (step p ps) q = step` p (simulateᴿ ps q)

correct : ∀ {e : Γ ⊢ T} {v : ⊨ T} → (δ ⊢ [] ↑ e ∼>* δ ⊢ [] ↓ v) → δ ⊢ e ⇓ v
correct {v = v} p = simulateᴿ p (` v)
\end{code}
