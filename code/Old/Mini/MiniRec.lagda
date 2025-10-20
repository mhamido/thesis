--------------------------------------------------------------------------------
-- This module is an extension of Mini2, adding recursive functions
--------------------------------------------------------------------------------

\begin{code}
module MiniRec where

open import Data.Bool renaming (Bool to 𝔹) using ()
open import Data.Nat using (ℕ)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong-app; subst)
\end{code}

--------------------------------------------------------------------------------
-- Defining the source language
--------------------------------------------------------------------------------

Types
\begin{code}
data Type : Set where
  Bool : Type
  Nat  : Type
  -- Add function types
  _⇒_  : Type → Type → Type
\end{code}

Importing contexts and environments
\begin{code}
open import Context Type
\end{code}


\begin{code}
private variable
  T T₁ T₂ Answer : Type
  Γ Δ : Context
\end{code}

Curch-style syntax with contexts
\begin{code}
data _⊢_ : Context → Type → Set where
  Num          : ℕ → Γ ⊢ Nat
  True         : Γ ⊢ Bool
  False        : Γ ⊢ Bool
  If_Then_Else : Γ ⊢ Bool → Γ ⊢ T → Γ ⊢ T → Γ ⊢ T
  _⊕_          : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Nat
  _⊝_          : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Nat
  _≈_          : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Bool
  Var          : T ∈ Γ → Γ ⊢ T
  Let_In_      : Γ ⊢ T₁ → (Γ , T₁) ⊢ T₂ → Γ ⊢ T₂
  ƛ_           : (Γ , T₁) ⊢ T₂ → Γ ⊢ (T₁ ⇒ T₂)
  _·_          : Γ ⊢ (T₁ ⇒ T₂) → Γ ⊢ T₁ → Γ ⊢ T₂
  LetRec_      : (Γ , T₁ ⇒ T₂ , T₁) ⊢ T₂ → Γ ⊢ (T₁ ⇒ T₂)
\end{code}

Values and environments have to be defined mutually because a closure
depends on an environment and vice versa.
\begin{code}
mutual 
  data Value : Type → Set where
    Nat      : ℕ → Value Nat
    Bool     : 𝔹 → Value Bool
    Closure  : Environment Γ → (Γ , T₁) ⊢ T₂ → Value (T₁ ⇒ T₂)
    -- Recursive closures as values
    RecClosure : Environment Γ → (Γ , T₁ ⇒ T₂ , T₁) ⊢ T₂ → Value (T₁ ⇒ T₂)

  open import Environment Type Value
\end{code}


\begin{code}
private variable
  e e₁ e₂ e₃ : Γ ⊢ T
  v v₁ v₂ : Value T
  n n₁ n₂ : Value Nat
  δ : Environment Γ
  δ' : Environment Δ
\end{code}

Some helper definitions
\begin{code}
true : Value Bool
true = (Bool Data.Bool.true)

false : Value Bool
false = (Bool Data.Bool.false)

_+_ : Value Nat → Value Nat → Value Nat
Nat a + Nat b = Nat (a Data.Nat.+ b)

_∸_ : Value Nat → Value Nat → Value Nat
Nat a ∸ Nat b = Nat (a Data.Nat.∸ b)

_≡ₙ_ : Value Nat → Value Nat → Value Bool
Nat 0 ≡ₙ Nat 0 = Bool 𝔹.true
Nat 0 ≡ₙ Nat (ℕ.suc b) = Bool 𝔹.false
Nat (ℕ.suc a) ≡ₙ Nat 0 = Bool 𝔹.false
Nat (ℕ.suc a) ≡ₙ Nat (ℕ.suc b) = Nat a ≡ₙ Nat b
\end{code}

Big-step semantics with environments
\begin{code}
data _⊢_⇓_ : Environment Γ → Γ ⊢ T → Value T → Set where
  NUM   : ∀ n → δ ⊢ (Num n) ⇓ (Nat n)
  TRUE  : δ ⊢ True ⇓ true
  FALSE : δ ⊢ False ⇓ false
  VAR   : ∀ (v : T ∈ Γ) → δ ⊢ (Var v) ⇓ lookupₑ δ v 
  IF₁   : ∀ {δ : Environment Γ} → δ ⊢ e₁ ⇓ true → δ ⊢ e₂ ⇓ v → (e₃ : Γ ⊢ T) → δ ⊢ If e₁ Then e₂ Else e₃ ⇓ v
  IF₂   : δ ⊢ e₁ ⇓ false → (e₂ : Γ ⊢ T) → δ ⊢ e₃ ⇓ v → δ ⊢ If e₁ Then e₂ Else e₃ ⇓ v
  ADD   : δ ⊢ e₁ ⇓ n₁ → δ ⊢ e₂ ⇓ n₂ → δ ⊢ (e₁ ⊕ e₂) ⇓ (n₁ + n₂)
  SUB   : δ ⊢ e₁ ⇓ n₁ → δ ⊢ e₂ ⇓ n₂ → δ ⊢ (e₁ ⊝ e₂) ⇓ (n₁ ∸ n₂)
  EQ    : δ ⊢ e₁ ⇓ n₁ → δ ⊢ e₂ ⇓ n₂ → δ ⊢ (e₁ ≈ e₂) ⇓ (n₁ ≡ₙ n₂)
  LET   : δ ⊢ e₁ ⇓ v₁ → (δ , v₁) ⊢ e₂ ⇓ v → δ ⊢ Let e₁ In e₂ ⇓ v
  FUN   : ∀ {δ : Environment Γ} → (e : (Γ , T₁) ⊢ T₂) → δ ⊢ (ƛ e) ⇓ (Closure δ e)
  APP   : ∀ {δ' : Environment Δ} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {e : (Δ , T₁) ⊢ T₂} {v₂ : Value T₁}
          → δ ⊢ e₁ ⇓ (Closure δ' e) → δ ⊢ e₂ ⇓ v₂ → ((δ' , v₂) ⊢ e ⇓ v) → δ ⊢ (e₁ · e₂) ⇓ v
  LETREC : (e : (Γ , T₁ ⇒ T₂ , T₁) ⊢ T₂) → δ ⊢ LetRec e ⇓ RecClosure δ e
  RECAPP : ∀ {δ' : Environment Δ} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {e : (Δ , T₁ ⇒ T₂ , T₁) ⊢ T₂} {v₂ : Value T₁}
           → δ ⊢ e₁ ⇓ (RecClosure δ' e) → δ ⊢ e₂ ⇓ v₂ → ((δ' , (RecClosure δ' e) , v₂) ⊢ e ⇓ v) → δ ⊢ (e₁ · e₂) ⇓ v
\end{code}

--------------------------------------------------------------------------------
-- Machine definition
--------------------------------------------------------------------------------

A hole is just a placeholder for some value
\begin{code}
data Hole : Set where
  ◌ : Hole
\end{code}

Stack frames with explicit holes
\begin{code}
data Frame : Type → Type → Set where
  If₁_Then_Else_ : Hole → Γ ⊢ T → Γ ⊢ T → Frame T Bool
  If₂_Then_Else_ : δ ⊢ e ⇓ true → Hole → Γ ⊢ T → Frame T T
  If₃_Then_Else_ : δ ⊢ e ⇓ false → Γ ⊢ T → Hole → Frame T T
  _⊕₁_           : Hole → Γ ⊢ Nat → Frame Nat Nat
  _⊕₂_           : δ ⊢ e ⇓ n → Hole → Frame Nat Nat
  _⊝₁_           : Hole → Γ ⊢ Nat → Frame Nat Nat
  _⊝₂_           : δ ⊢ e ⇓ n → Hole → Frame Nat Nat
  _≈₁_           : Hole → Γ ⊢ Nat → Frame Bool Nat
  _≈₂_           : δ ⊢ e ⇓ n → Hole → Frame Bool Nat
  Let₁_In_       : Hole → (Γ , T₁) ⊢ T₂ → Frame T₂ T₁
  Let₂_In_       : δ ⊢ e ⇓ v → Hole → Frame T₂ T₂
  -- Interestingly _·_ has only two arguments but 3 sub-trees, thus we need 3 frames
  -- Since we don't know the expression we get from the closure we technically have
  -- 2 holes in one frame
  App₁           : Hole → Γ ⊢ T₁ → Frame T (T₁ ⇒ T₂)
  App₂           : δ ⊢ e₁ ⇓ v₁ → Hole → Frame T T₁
  App₃           : δ ⊢ e₁ ⇓ v₁ → δ ⊢ e₂ ⇓ v₂ → Hole → Frame T T₁
  RecApp₁        : Hole → Γ ⊢ T₁ → Frame T (T₁ ⇒ T₂)
  RecApp₂        : δ ⊢ e₁ ⇓ v₁ → Hole → Frame T T₁
  RecApp₃        : δ ⊢ e₁ ⇓ v₁ → δ ⊢ e₂ ⇓ v₂ → Hole → Frame T T₁
\end{code}

Stack
\begin{code}
data Stack (Answer : Type) : Type → Set where
  []  : Stack Answer Answer
  _∷_ : Stack Answer T₁ → Frame T₁ T₂ → Stack Answer T₂
\end{code}

Machine state
Going up the tree, aka. eval: ↑
Going down the tree, aka. return: ↓
NEW: We extend both constructors with an environment δ mapping variables to values
\begin{code}
data State (Answer : Type) : Set where
  _⊢_↓_ : {Γ : Context} → (δ : Environment Γ) → Stack Answer T → {e : Γ ⊢ T} → δ ⊢ e ⇓ v → State Answer
  _⊢_↑_ : (δ : Environment Γ) → Stack Answer T → Γ ⊢ T → State Answer
\end{code}

Step relation
\begin{code}
data _⇾_ : State T → State T → Set where
  step-If₁-true  : ∀ {e₁ : Γ ⊢ Bool} {e₂ e₃ : Γ ⊢ T} {p₁ : δ ⊢ e₁ ⇓ true} {stack : Stack Answer T}
                   → (δ ⊢ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↓ p₁) ⇾ (δ ⊢ (stack ∷ (If₂ p₁ Then ◌ Else e₃)) ↑ e₂)
  step-If₁-false : ∀ {δ : Environment Γ} {e₁ : Γ ⊢ Bool} {e₂ e₃ : Γ ⊢ T} {p₁ : δ ⊢ e₁ ⇓ false} {stack : Stack Answer T}
                   → (δ ⊢ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↓ p₁) ⇾ (δ ⊢ (stack ∷ (If₃ p₁ Then e₂ Else ◌)) ↑ e₃)
  step-If₂       : ∀ {e₁ : Γ ⊢ Bool} {e₂ e₃ : Γ ⊢ T} {p₁ : δ ⊢ e₁ ⇓ true} {p₂ : δ ⊢ e₂ ⇓ v} {stack : Stack Answer T}
                   → (δ ⊢ (stack ∷ (If₂ p₁ Then ◌ Else e₃)) ↓ p₂) ⇾ (δ ⊢ stack ↓ IF₁ p₁ p₂ e₃)
  step-If₃       : ∀ {e₁ : Γ ⊢ Bool} {e₂ e₃ : Γ ⊢ T} {p₁ : δ ⊢ e₁ ⇓ false} {p₃ : δ ⊢ e₃ ⇓ v} {stack : Stack Answer T}
                   → (δ ⊢ (stack ∷ (If₃ p₁ Then e₂ Else ◌)) ↓ p₃) ⇾ (δ ⊢ stack ↓ IF₂ p₁ e₂ p₃)
  step-⊕₁        : ∀ {e₁ e₂ : Γ ⊢ Nat} {p₁ : δ ⊢ e₁ ⇓ n₁} {stack : Stack Answer Nat}
                   → (δ ⊢ (stack ∷ (◌ ⊕₁ e₂)) ↓ p₁) ⇾ (δ ⊢ (stack ∷ (p₁ ⊕₂ ◌)) ↑ e₂)
  step-⊕₂        : ∀ {e₁ e₂ : Γ ⊢ Nat} {p₁ : δ ⊢ e₁ ⇓ n₁} {p₂ : δ ⊢ e₂ ⇓ n₂} {stack : Stack Answer Nat}
                   → (δ ⊢ (stack ∷ (p₁ ⊕₂ ◌)) ↓ p₂) ⇾ (δ ⊢ stack ↓ ADD p₁ p₂)
  step-⊝₁        : ∀ {e₁ e₂ : Γ ⊢ Nat} {p₁ : δ ⊢ e₁ ⇓ n₁} {stack : Stack Answer Nat}
                   → (δ ⊢ (stack ∷ (◌ ⊝₁ e₂)) ↓ p₁) ⇾ (δ ⊢ (stack ∷ (p₁ ⊝₂ ◌)) ↑ e₂)
  step-⊝₂        : ∀ {e₁ e₂ : Γ ⊢ Nat} {p₁ : δ ⊢ e₁ ⇓ n₁} {p₂ : δ ⊢ e₂ ⇓ n₂} {stack : Stack Answer Nat}
                   → (δ ⊢ (stack ∷ (p₁ ⊝₂ ◌)) ↓ p₂) ⇾ (δ ⊢ stack ↓ SUB p₁ p₂)
  step-≈₁        : ∀ {e₁ e₂ : Γ ⊢ Nat} {p₁ : δ ⊢ e₁ ⇓ n₁} {stack : Stack Answer Bool}
                   → (δ ⊢ (stack ∷ (◌ ≈₁ e₂)) ↓ p₁) ⇾ (δ ⊢ (stack ∷ (p₁ ≈₂ ◌)) ↑ e₂)
  step-≈₂        : ∀ {e₁ e₂ : Γ ⊢ Nat} {p₁ : δ ⊢ e₁ ⇓ n₁} {p₂ : δ ⊢ e₂ ⇓ n₂} {stack : Stack Answer Bool} 
                   → (δ ⊢ (stack ∷ (p₁ ≈₂ ◌)) ↓ p₂) ⇾ (δ ⊢ stack ↓ EQ p₁ p₂)
  step-Let₁      : ∀ {e₁ : Γ ⊢ T₁} {e₂ : (Γ , T₁) ⊢ T₂} {p₁ : δ ⊢ e₁ ⇓ v₁} {stack : Stack Answer T₂}
                 → (δ ⊢ stack ∷ (Let₁ ◌ In e₂) ↓ p₁) ⇾ ((δ , v₁) ⊢ stack ∷ (Let₂ p₁ In ◌) ↑ e₂)
  step-Let₂      : ∀ {e₁ : Γ ⊢ T₁} {e₂ : (Γ , T₁) ⊢ T₂} {p₁ : δ ⊢ e₁ ⇓ v₁} {p₂ : (δ , v₁) ⊢ e₂ ⇓ v₂}
                     {stack : Stack Answer T₂}
                 → ((δ , v₁) ⊢ stack ∷ (Let₂ p₁ In ◌) ↓ p₂) ⇾ (δ ⊢ stack ↓ LET p₁ p₂)
  -- Original transitions for function application
  --step-·₁      : ∀ {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {δ' : Environment Δ} {e : (Δ , T₁) ⊢ T₂} {e₂ : Γ ⊢ T₁} {p₁ : δ ⊢ e₁ ⇓ (Closure δ' e)} {stack : Stack Answer T₂}
  --               → (δ ⊢ stack ∷ (◌ ·₁ e₂) ↓ p₁) ⇾ (δ ⊢ stack ∷ (p₁ ·₂ ◌) ↑ e₂)
  --step-·₂      : ∀ {stack : Stack Answer T₂} {δ' : Environment Δ} {e : (Δ , T₁) ⊢ T₂} {v : Value T₂} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {v₂ : Value T₁} {v : (δ' , v₂) ⊢ e ⇓ v} {p₁ : δ ⊢ e₁ ⇓ (Closure δ' e)} {p₂ : δ ⊢ e₂ ⇓ v₂}
  --               → (δ ⊢ stack ∷ (p₁ ·₂ ◌) ↓ p₂) ⇾ (δ ⊢ stack ↓ APP p₁ p₂ v)
  --step-·         : ∀ {stack : Stack Answer T₂}
  --                 → (δ ⊢ stack ↑ (e₁ · e₂)) ⇾ (δ ⊢ (stack ∷ (◌ ·₁ e₂)) ↑ e₁)
  step-App₁    : ∀ {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {δ' : Environment Δ} {e : (Δ , T₁) ⊢ T₂} {e₂ : Γ ⊢ T₁} {p₁ : δ ⊢ e₁ ⇓ (Closure δ' e)} {stack : Stack Answer T₂}
                 → (δ ⊢ stack ∷ (App₁ ◌ e₂) ↓ p₁) ⇾ (δ ⊢ stack ∷ (App₂ p₁ ◌) ↑ e₂)
  step-App₂    : ∀ {stack : Stack Answer T₂} {δ' : Environment Δ} {e : (Δ , T₁) ⊢ T₂} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {v₂ : Value T₁} {p₁ : δ ⊢ e₁ ⇓ (Closure δ' e)} {p₂ : δ ⊢ e₂ ⇓ v₂}
                 → (δ ⊢ stack ∷ (App₂ p₁ ◌) ↓ p₂) ⇾ ((δ' , v₂) ⊢ stack ∷ (App₃ p₁ p₂ ◌) ↑ e)
  step-App₃    : ∀ {stack : Stack Answer T₂} {δ' : Environment Δ} {e : (Δ , T₁) ⊢ T₂} {v : Value T₂} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {v₂ : Value T₁} {p₃ : (δ' , v₂) ⊢ e ⇓ v} {p₁ : δ ⊢ e₁ ⇓ (Closure δ' e)} {p₂ : δ ⊢ e₂ ⇓ v₂}
                 → ((δ' , v₂) ⊢ stack ∷ (App₃ p₁ p₂ ◌) ↓ p₃) ⇾ (δ ⊢ stack ↓ (APP p₁ p₂ p₃))
  -- Move from App₁ frame to a RecApp₂ frame. Otherwise we can't distinguish normal function application and recursive ones
  step-RecApp₁ : ∀ {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {δ' : Environment Δ} {e : (Δ , T₁ ⇒ T₂ , T₁) ⊢ T₂} {e₂ : Γ ⊢ T₁} {p₁ : δ ⊢ e₁ ⇓ (RecClosure δ' e)} {stack : Stack Answer T₂}
                 → (δ ⊢ stack ∷ (App₁ ◌ e₂) ↓ p₁) ⇾ (δ ⊢ stack ∷ (RecApp₂ p₁ ◌) ↑ e₂)
  step-RecApp₂ : ∀ {stack : Stack Answer T₂} {δ' : Environment Δ} {e : (Δ , T₁ ⇒ T₂ , T₁) ⊢ T₂} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {v₂ : Value T₁} {p₁ : δ ⊢ e₁ ⇓ (RecClosure δ' e)} {p₂ : δ ⊢ e₂ ⇓ v₂}
                 → (δ ⊢ stack ∷ (RecApp₂ p₁ ◌) ↓ p₂) ⇾ ((δ' , (RecClosure δ' e) , v₂) ⊢ stack ∷ (RecApp₃ p₁ p₂ ◌) ↑ e)
  step-RecApp₃ : ∀ {stack : Stack Answer T₂} {δ' : Environment Δ} {e : (Δ , T₁ ⇒ T₂ , T₁) ⊢ T₂} {v : Value T₂} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {v₂ : Value T₁} {p₃ : (δ' , (RecClosure δ' e) , v₂) ⊢ e ⇓ v} {p₁ : δ ⊢ e₁ ⇓ (RecClosure δ' e)} {p₂ : δ ⊢ e₂ ⇓ v₂}
                 → ((δ' , (RecClosure δ' e) , v₂) ⊢ stack ∷ (RecApp₃ p₁ p₂ ◌) ↓ p₃) ⇾ (δ ⊢ stack ↓ (RECAPP p₁ p₂ p₃))

  step-True      : ∀ {stack : Stack Answer Bool}
                   → (δ ⊢ stack ↑ True) ⇾ (δ ⊢ stack ↓ TRUE)
  step-False     : ∀ {stack : Stack Answer Bool}
                   → (δ ⊢ stack ↑ False) ⇾ (δ ⊢ stack ↓ FALSE)
  step-Num       : ∀ {n : ℕ} {stack : Stack Answer Nat}
                   → (δ ⊢ stack ↑ Num n) ⇾ (δ ⊢ stack ↓ NUM n)
  step-ƛ         : ∀ {stack : Stack Answer (T₁ ⇒ T₂)} {e : (Γ , T₁) ⊢ T₂} {δ : Environment Γ}
                   → (δ ⊢ stack ↑ (ƛ e)) ⇾ (δ ⊢ stack ↓ FUN e)
  step-Var       : ∀ {v : T ∈ Γ} {stack : Stack Answer T}
                   → (δ ⊢ stack ↑ Var v) ⇾ (δ ⊢ stack ↓ VAR v)
  step-If        : ∀ {e₁ : Γ ⊢ Bool} {e₂ e₃ : Γ ⊢ T} {p₁ : δ ⊢ e₁ ⇓ v} {stack : Stack Answer T}
                   → (δ ⊢ stack ↑ If e₁ Then e₂ Else e₃) ⇾ (δ ⊢ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↑ e₁)
  step-⊕         : ∀ {e₁ e₂ : Γ ⊢ Nat} {stack : Stack Answer Nat}
                   → (δ ⊢ stack ↑ (e₁ ⊕ e₂)) ⇾ (δ ⊢ (stack ∷ (◌ ⊕₁ e₂)) ↑ e₁)
  step-⊝         : ∀ {e₁ e₂ : Γ ⊢ Nat} {stack : Stack Answer Nat}
                   → (δ ⊢ stack ↑ (e₁ ⊝ e₂)) ⇾ (δ ⊢ (stack ∷ (◌ ⊝₁ e₂)) ↑ e₁)
  step-≈         : ∀ {e₁ e₂ : Γ ⊢ Nat} {stack : Stack Answer Bool}
                   → (δ ⊢ stack ↑ (e₁ ≈ e₂)) ⇾ (δ ⊢ (stack ∷ (◌ ≈₁ e₂)) ↑ e₁)
  step-Let       : ∀ {stack : Stack Answer T₂}
                   → (δ ⊢ stack ↑ (Let e₁ In e₂)) ⇾ (δ ⊢ (stack ∷ (Let₁ ◌ In e₂)) ↑ e₁)
  step-LetRec    : ∀ {stack : Stack Answer (T₁ ⇒ T₂)} {e : (Γ , T₁ ⇒ T₂ , T₁) ⊢ T₂}
                   → (δ ⊢ stack ↑ (LetRec e)) ⇾ (δ ⊢ stack ↓ LETREC e)
  step-App       : ∀ {stack : Stack Answer T₂}
                   → (δ ⊢ stack ↑ (e₁ · e₂)) ⇾ (δ ⊢ (stack ∷ (App₁ ◌ e₂)) ↑ e₁)
\end{code}

Transitive, reflexive closure of the step relation
\begin{code}
data _↠_ : State T → State T → Set where
  base  : ∀ {s : State T}        → s ↠ s
  step  : ∀ {s₁ s₂ s₃ : State T} → s₁ ⇾ s₂ → s₂ ↠ s₃ → s₁ ↠ s₃

↠-reflexive : ∀ {s : State Answer} → s ↠ s
↠-reflexive = base

↠-transitive : ∀ {s₀ s₁ s₂ : State Answer} → s₀ ↠ s₁ → s₁ ↠ s₂ → s₀ ↠ s₂
↠-transitive (base)      q = q
↠-transitive (step s p)  q = step s (↠-transitive p q)
\end{code}

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

\begin{code}
infix  0 proof_
infixr 1 ⇾-link ↠-link
infix  2 _∎

proof_ : {s₁ s₂ : State Answer} → s₁ ↠ s₂ → s₁ ↠ s₂
proof s₁⇾⃰s₂ = s₁⇾⃰s₂

syntax ⇾-link x q p = x ⇾⟨ p ⟩ q
⇾-link : (s₀ : State Answer) {s₁ s₂ : State Answer} → s₁ ↠ s₂ → s₀ ⇾ s₁ → s₀ ↠ s₂
⇾-link _ q p = step p q

syntax ↠-link x q p = x ↠⟨ p ⟩ q
↠-link : (s₀ : State Answer) {s₁ s₂ : State Answer} → s₁ ↠ s₂ → s₀ ↠ s₁ → s₀ ↠ s₂
↠-link _ q p = ↠-transitive p q

_∎ : (s : State Answer) → s ↠ s
e ∎ = ↠-reflexive
\end{code}


Trivial proof of correctness
\begin{code}
correct : ∀ (e : Γ ⊢ T) → (v : Value T) → (p : δ ⊢ e ⇓ v) →
  (δ ⊢ [] ↑ e) ↠ (δ ⊢ [] ↓ p) → δ ⊢ e ⇓ v
correct _ _ p _ = p
\end{code}

Completeness
\begin{code}
complete : ∀ (δ : Environment Γ) (stack : Stack Answer T) (e : Γ ⊢ T) (v : Value T) →
  (p : δ ⊢ e ⇓ v) → (δ ⊢ stack ↑ e) ↠ (δ ⊢ stack ↓ p)
complete {Γ = Γ} δ stack (Num x) _ (NUM .x) = step step-Num base
complete δ stack True _ TRUE        = step step-True base
complete δ stack False _ FALSE      = step step-False base
complete δ stack (Var e) v (VAR p) = step step-Var base
complete δ stack (If e₁ Then e₂ Else e₃) v (IF₁ p₁ p₂ .e₃) =
  proof
    (δ ⊢ stack ↑ If e₁ Then e₂ Else e₃)
  ⇾⟨ step-If {p₁ = p₁} ⟩
    (δ ⊢ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↑ e₁)
  ↠⟨ complete δ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) e₁ true p₁ ⟩
    (δ ⊢ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↓ p₁)
  ⇾⟨ step-If₁-true ⟩
    (δ ⊢ (stack ∷ (If₂ p₁ Then ◌ Else e₃)) ↑ e₂)
  ↠⟨ complete δ (stack ∷ (If₂ p₁ Then ◌ Else e₃)) e₂ v p₂ ⟩
    (δ ⊢ (stack ∷ (If₂ p₁ Then ◌ Else e₃)) ↓ p₂)
  ⇾⟨ step-If₂ ⟩
    (δ ⊢ stack ↓ IF₁ p₁ p₂ e₃)
  ∎
complete δ stack (If e₁ Then e₂ Else e₃) v (IF₂ p₁ .e₂ p₃) = 
  proof
    (δ ⊢ stack ↑ If e₁ Then e₂ Else e₃)
  ⇾⟨ step-If {p₁ = p₁} ⟩
    (δ ⊢ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↑ e₁)
  ↠⟨ complete δ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) e₁ false p₁ ⟩
    (δ ⊢ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↓ p₁)
  ⇾⟨ step-If₁-false ⟩
   (δ ⊢ (stack ∷ (If₃ p₁ Then e₂ Else ◌)) ↑ e₃)
  ↠⟨ complete δ (stack ∷ (If₃ p₁ Then e₂ Else ◌)) e₃ v p₃ ⟩
    (δ ⊢ (stack ∷ (If₃ p₁ Then e₂ Else ◌)) ↓ p₃)
  ⇾⟨ step-If₃ ⟩
    (δ ⊢ stack ↓ IF₂ p₁ e₂ p₃)
  ∎
complete δ stack (e₁ ⊕ e₂) v (ADD p₁ p₂) =
  proof
    (δ ⊢ stack ↑ (e₁ ⊕ e₂))
  ⇾⟨ step-⊕ ⟩
    (δ ⊢ (stack ∷ (◌ ⊕₁ e₂)) ↑ e₁)
  ↠⟨ complete δ (stack ∷ (◌ ⊕₁ e₂)) e₁ _ p₁ ⟩
    (δ ⊢ (stack ∷ (◌ ⊕₁ e₂)) ↓ p₁)
  ⇾⟨ step-⊕₁ ⟩
    (δ ⊢ (stack ∷ (p₁ ⊕₂ ◌)) ↑ e₂)
  ↠⟨ complete δ (stack ∷ (p₁ ⊕₂ ◌)) e₂ _ p₂ ⟩
    (δ ⊢ (stack ∷ (p₁ ⊕₂ ◌)) ↓ p₂)
  ⇾⟨ step-⊕₂ ⟩
    (δ ⊢ stack ↓ ADD p₁ p₂)
  ∎
complete δ stack (e₁ ⊝ e₂) v (SUB p₁ p₂) =
  proof
    (δ ⊢ stack ↑ (e₁ ⊝ e₂))
  ⇾⟨ step-⊝ ⟩
    (δ ⊢ (stack ∷ (◌ ⊝₁ e₂)) ↑ e₁)
  ↠⟨ complete δ (stack ∷ (◌ ⊝₁ e₂)) e₁ _ p₁ ⟩
    (δ ⊢ (stack ∷ (◌ ⊝₁ e₂)) ↓ p₁)
  ⇾⟨ step-⊝₁ ⟩
    (δ ⊢ (stack ∷ (p₁ ⊝₂ ◌)) ↑ e₂)
  ↠⟨ complete δ (stack ∷ (p₁ ⊝₂ ◌)) e₂ _ p₂ ⟩
    (δ ⊢ (stack ∷ (p₁ ⊝₂ ◌)) ↓ p₂)
  ⇾⟨ step-⊝₂ ⟩
    (δ ⊢ stack ↓ SUB p₁ p₂)
  ∎
complete δ stack (e₁ ≈ e₂) v (EQ p₁ p₂) =
  proof
    (δ ⊢ stack ↑ (e₁ ≈ e₂))
  ⇾⟨ step-≈ ⟩
    (δ ⊢ (stack ∷ (◌ ≈₁ e₂)) ↑ e₁)
  ↠⟨ complete δ (stack ∷ (◌ ≈₁ e₂)) e₁ _ p₁ ⟩
    (δ ⊢ (stack ∷ (◌ ≈₁ e₂)) ↓ p₁)
  ⇾⟨ step-≈₁ ⟩
    (δ ⊢ (stack ∷ (p₁ ≈₂ ◌)) ↑ e₂)
  ↠⟨ complete δ (stack ∷ (p₁ ≈₂ ◌)) e₂ _ p₂ ⟩
    (δ ⊢ (stack ∷ (p₁ ≈₂ ◌)) ↓ p₂)
  ⇾⟨ step-≈₂ ⟩
    (δ ⊢ stack ↓ EQ p₁ p₂)
  ∎
complete δ stack (Let e₁ In e₂) v (LET {v₁ = v₁} p₁ p₂) =
  proof
    (δ ⊢ stack ↑ (Let e₁ In e₂))
  ⇾⟨ step-Let ⟩
    (δ ⊢ (stack ∷ (Let₁ ◌ In e₂)) ↑ e₁)
  ↠⟨ complete δ (stack ∷ (Let₁ ◌ In e₂)) e₁ _ p₁ ⟩
    (δ ⊢ (stack ∷ (Let₁ ◌ In e₂)) ↓ p₁)
  ⇾⟨ step-Let₁ ⟩
    ((δ , v₁) ⊢ (stack ∷ (Let₂ p₁ In ◌)) ↑ e₂)
  ↠⟨ complete (δ , v₁) (stack ∷ (Let₂ p₁ In ◌)) e₂ _ p₂ ⟩
    ((δ , v₁) ⊢ (stack ∷ (Let₂ p₁ In ◌)) ↓ p₂)
  ⇾⟨ step-Let₂ ⟩
    (δ ⊢ stack ↓ LET p₁ p₂)
  ∎
complete δ stack (ƛ e) v (FUN e) = step step-ƛ base
complete δ stack (e₁ · e₂) v (APP {δ' = δ'} {e = e} {v₂ = v₂} p₁ p₂ p₃) =
  proof
    (δ ⊢ stack ↑ (e₁ · e₂))
  ⇾⟨ step-App ⟩
    (δ ⊢ stack ∷ (App₁ ◌ e₂) ↑ e₁)
  ↠⟨ complete δ (stack ∷ (App₁ ◌ e₂)) e₁ _ p₁ ⟩
    (δ ⊢ stack ∷ (App₁ ◌ e₂) ↓ p₁)
  ⇾⟨ step-App₁ ⟩
    (δ ⊢ stack ∷ (App₂ p₁ ◌) ↑ e₂)
  ↠⟨ complete δ (stack ∷ (App₂ p₁ ◌)) e₂ _ p₂ ⟩
    (δ ⊢ stack ∷ (App₂ p₁ ◌) ↓ p₂)
  ⇾⟨ step-App₂ ⟩
    ((δ' , v₂) ⊢ stack ∷ App₃ p₁ p₂ ◌ ↑ e)
  ↠⟨ complete (δ' , v₂) (stack ∷ (App₃ p₁ p₂ ◌)) e _ p₃ ⟩
    ((δ' , v₂) ⊢ stack ∷ (App₃ p₁ p₂ ◌) ↓ p₃)
  ⇾⟨ step-App₃ ⟩
    (δ ⊢ stack ↓ APP p₁ p₂ p₃)
  ∎
complete δ stack (LetRec e) v (LETREC p) = step step-LetRec base
complete δ stack (e₁ · e₂) v (RECAPP {δ' = δ'} {e = e} {v₂ = v₂} p₁ p₂ p₃) =
  proof
    (δ ⊢ stack ↑ (e₁ · e₂))
  ⇾⟨ step-App ⟩
    (δ ⊢ stack ∷ App₁ ◌ e₂ ↑ e₁)
  ↠⟨ complete δ (stack ∷ App₁ ◌ e₂) e₁ (RecClosure δ' e) p₁ ⟩
    (δ ⊢ stack ∷ App₁ ◌ e₂ ↓ p₁)
  ⇾⟨ step-RecApp₁ ⟩
    (δ ⊢ stack ∷ RecApp₂ p₁ ◌ ↑ e₂)
  ↠⟨ complete δ (stack ∷ RecApp₂ p₁ ◌) e₂ _ p₂ ⟩
    (δ ⊢ stack ∷ RecApp₂ p₁ ◌ ↓ p₂)
  ⇾⟨ step-RecApp₂ ⟩
    ((δ' , RecClosure δ' e , v₂) ⊢ stack ∷ RecApp₃ p₁ p₂ ◌ ↑ e)
  ↠⟨ complete (δ' , RecClosure δ' e , v₂) (stack ∷ RecApp₃ p₁ p₂ ◌) e v p₃ ⟩
    ((δ' , RecClosure δ' e , v₂) ⊢ stack ∷ RecApp₃ p₁ p₂ ◌ ↓ p₃)
  ⇾⟨ step-RecApp₃ ⟩
    (δ ⊢ stack ↓ RECAPP p₁ p₂ p₃)
  ∎
\end{code}

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

Example of the recursive sum function with sum 2 = 3
\begin{code}
example-rec : ∅ ⊢ (LetRec If (Var Z ≈ Num 0) Then (Num 0) Else (Var Z ⊕ (Var (S Z) · (Var Z ⊝ Num 1)))) · Num 2 ⇓ Nat 3
example-rec = RECAPP 
                (LETREC 
                  (If Var Z ≈ Num ℕ.zero Then Num ℕ.zero Else (Var Z ⊕ (Var (S Z) · (Var Z ⊝ Num 1))))) (NUM 2) (IF₂
                    (EQ (VAR Z) (NUM 0)) (Num 0) (ADD
                      (VAR Z) (RECAPP
                        (VAR (S Z)) (SUB (VAR Z) (NUM 1)) (IF₂
                          (EQ (VAR Z) (NUM 0)) (Num 0) (ADD
                            (VAR Z) (RECAPP
                              (VAR (S Z)) (SUB (VAR Z) (NUM 1)) (IF₁
                                (EQ (VAR Z) (NUM 0)) (NUM 0) (Var Z ⊕ (Var (S Z) · (Var Z ⊝ Num 1))))))))))
\end{code}

The abstract machine also evaluates the above expression with the same result
\begin{code}
example-rec-machine : (∅ ⊢ [] ↑ ((LetRec If (Var Z ≈ Num 0) Then (Num 0) Else (Var Z ⊕ (Var (S Z) · (Var Z ⊝ Num 1)))) · Num 2)) ↠ (∅ ⊢ [] ↓ _)
example-rec-machine = complete ∅ [] ((LetRec If Var Z ≈ Num 0 Then Num 0 Else (Var Z ⊕ (Var (S Z) · (Var Z ⊝ Num 1)))) · Num 2) (Nat 3) example-rec
\end{code}

1 + 1 = 2 as an example
\begin{code}
example0 : (∅ ⊢ [] ↑ (Num 1 ⊕ Num 1)) ↠ (∅ ⊢ [] ↓ _)
example0 = step step-⊕ (step step-Num (step step-⊕₁ (step step-Num (step step-⊕₂ base))))
\end{code}
