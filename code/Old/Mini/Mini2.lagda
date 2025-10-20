--------------------------------------------------------------------------------
-- This module is an extension of Mini, adding let-bindings
--------------------------------------------------------------------------------

\begin{code}
module Mini2 where

open import Data.Bool renaming (Bool to 𝔹) using ()
open import Data.Nat using (ℕ)
\end{code}

--------------------------------------------------------------------------------
-- Defining the source language
--------------------------------------------------------------------------------

Types
\begin{code}
data Type : Set where
  Bool : Type
  Nat  : Type
\end{code}

Values
\begin{code}
data Value : Type → Set where
  Nat  : ℕ → Value Nat
  Bool : 𝔹 → Value Bool
\end{code}

Importing contexts and environments
\begin{code}
open import Context Type
open import Environment Type Value
\end{code}

\begin{code}
private variable
  T T₁ T₂ Answer : Type
  Γ : Context
\end{code}

Curch-style syntax with contexts
\begin{code}
data _⊢_ : Context → Type → Set where
  Num          : ℕ → Γ ⊢ Nat
  True         : Γ ⊢ Bool
  False        : Γ ⊢ Bool
  If_Then_Else : Γ ⊢ Bool → Γ ⊢ T → Γ ⊢ T → Γ ⊢ T
  _⊕_          : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Nat
  Var          : T ∈ Γ → Γ ⊢ T
  Let_In_      : Γ ⊢ T₁ → (Γ , T₁) ⊢ T₂ → Γ ⊢ T₂
\end{code}

\begin{code}
private variable
  e e₁ e₂ e₃ : Γ ⊢ T
  v v₁ v₂ : Value T
  n n₁ n₂ : Value Nat
  δ : Environment Γ
\end{code}

Some helper definitions
\begin{code}
true : Value Bool
true = (Bool Data.Bool.true)

false : Value Bool
false = (Bool Data.Bool.false)

_+_ : Value Nat → Value Nat → Value Nat
Nat a + Nat b = Nat (a Data.Nat.+ b)
\end{code}

Big-step semantics with environments
\begin{code}
data _⊢_⇓_ : Environment Γ → Γ ⊢ T → Value T → Set where
  NUM   : ∀ n → δ ⊢ (Num n) ⇓ (Nat n)
  TRUE  : δ ⊢ True ⇓ true
  FALSE : δ ⊢ False ⇓ false
  VAR   : ∀ (v : T ∈ Γ) → δ ⊢ (Var v) ⇓ lookupₑ δ v 
  IF₁   : δ ⊢ e₁ ⇓ true → δ ⊢ e₂ ⇓ v → (e₃ : Γ ⊢ T) → δ ⊢ If e₁ Then e₂ Else e₃ ⇓ v
  IF₂   : δ ⊢ e₁ ⇓ false → (e₂ : Γ ⊢ T) → δ ⊢ e₃ ⇓ v → δ ⊢ If e₁ Then e₂ Else e₃ ⇓ v
  ADD   : δ ⊢ e₁ ⇓ n₁ → δ ⊢ e₂ ⇓ n₂ → δ ⊢ (e₁ ⊕ e₂) ⇓ (n₁ + n₂)
  LET   : δ ⊢ e₁ ⇓ v₁ → (δ , v₁) ⊢ e₂ ⇓ v → δ ⊢ Let e₁ In e₂ ⇓ v
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
  Let₁_In_       : Hole → (Γ , T₁) ⊢ T₂ → Frame T₂ T₁
  Let₂_In_       : δ ⊢ e ⇓ v → Hole → Frame T₂ T₂
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
  _⊢_↓_ : (δ : Environment Γ) → Stack Answer T → {e : Γ ⊢ T} → δ ⊢ e ⇓ v → State Answer
  _⊢_↑_ : (δ : Environment Γ) → Stack Answer T → Γ ⊢ T → State Answer
\end{code}

Step relation
\begin{code}
data _⇾_ : State T → State T → Set where
  step-If₁-true  : ∀ {e₁ : Γ ⊢ Bool} {e₂ e₃ : Γ ⊢ T} {p₁ : δ ⊢ e₁ ⇓ true} {stack : Stack Answer T}
                   → (δ ⊢ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↓ p₁) ⇾ (δ ⊢ (stack ∷ (If₂ p₁ Then ◌ Else e₃)) ↑ e₂)
  step-If₁-false : ∀ {e₁ : Γ ⊢ Bool} {e₂ e₃ : Γ ⊢ T} {p₁ : δ ⊢ e₁ ⇓ false} {stack : Stack Answer T}
                   → (δ ⊢ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↓ p₁) ⇾ (δ ⊢ (stack ∷ (If₃ p₁ Then e₂ Else ◌)) ↑ e₃)
  step-If₂       : ∀ {e₁ : Γ ⊢ Bool} {e₂ e₃ : Γ ⊢ T} {p₁ : δ ⊢ e₁ ⇓ true} {p₂ : δ ⊢ e₂ ⇓ v} {stack : Stack Answer T}
                   → (δ ⊢ (stack ∷ (If₂ p₁ Then ◌ Else e₃)) ↓ p₂) ⇾ (δ ⊢ stack ↓ IF₁ p₁ p₂ e₃)
  step-If₃       : ∀ {e₁ : Γ ⊢ Bool} {e₂ e₃ : Γ ⊢ T} {p₁ : δ ⊢ e₁ ⇓ false} {p₃ : δ ⊢ e₃ ⇓ v} {stack : Stack Answer T}
                   → (δ ⊢ (stack ∷ (If₃ p₁ Then e₂ Else ◌)) ↓ p₃) ⇾ (δ ⊢ stack ↓ IF₂ p₁ e₂ p₃)
  step-⊕₁        : ∀ {e₁ e₂ : Γ ⊢ Nat} {p₁ : δ ⊢ e₁ ⇓ n₁} {stack : Stack Answer Nat}
                   → (δ ⊢ (stack ∷ (◌ ⊕₁ e₂)) ↓ p₁) ⇾ (δ ⊢ (stack ∷ (p₁ ⊕₂ ◌)) ↑ e₂)
  step-⊕₂        : ∀ {e₁ e₂ : Γ ⊢ Nat} {p₁ : δ ⊢ e₁ ⇓ n₁} {p₂ : δ ⊢ e₂ ⇓ n₂} {stack : Stack Answer Nat}
                   → (δ ⊢ (stack ∷ (p₁ ⊕₂ ◌)) ↓ p₂) ⇾ (δ ⊢ stack ↓ ADD p₁ p₂)
  step-Let₁      : ∀ {e₁ : Γ ⊢ T₁} {e₂ : (Γ , T₁) ⊢ T₂} {p₁ : δ ⊢ e₁ ⇓ v₁} {stack : Stack Answer T₂}
                 → (δ ⊢ stack ∷ (Let₁ ◌ In e₂) ↓ p₁) ⇾ ((δ , v₁) ⊢ stack ∷ (Let₂ p₁ In ◌) ↑ e₂)
  step-Let₂      : ∀ {e₁ : Γ ⊢ T₁} {e₂ : (Γ , T₁) ⊢ T₂} {p₁ : δ ⊢ e₁ ⇓ v₁} {p₂ : (δ , v₁) ⊢ e₂ ⇓ v₂}
                     {stack : Stack Answer T₂}
                 → ((δ , v₁) ⊢ stack ∷ (Let₂ p₁ In ◌) ↓ p₂) ⇾ (δ ⊢ stack ↓ LET p₁ p₂)

  step-True      : ∀ {stack : Stack Answer Bool}
                   → (δ ⊢ stack ↑ True) ⇾ (δ ⊢ stack ↓ TRUE)
  step-False     : ∀ {stack : Stack Answer Bool}
                   → (δ ⊢ stack ↑ False) ⇾ (δ ⊢ stack ↓ FALSE)
  step-Num       : ∀ {n : ℕ} {stack : Stack Answer Nat}
                   → (δ ⊢ stack ↑ Num n) ⇾ (δ ⊢ stack ↓ NUM n)
  step-Var       : ∀ {v : T ∈ Γ} {stack : Stack Answer T}
                   → (δ ⊢ stack ↑ Var v) ⇾ (δ ⊢ stack ↓ VAR v)
  step-If        : ∀ {e₁ : Γ ⊢ Bool} {e₂ e₃ : Γ ⊢ T} {p₁ : δ ⊢ e₁ ⇓ v} {stack : Stack Answer T}
                   → (δ ⊢ stack ↑ If e₁ Then e₂ Else e₃) ⇾ (δ ⊢ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↑ e₁)
  step-⊕         : ∀ {e₁ e₂ : Γ ⊢ Nat} {stack : Stack Answer Nat}
                   → (δ ⊢ stack ↑ (e₁ ⊕ e₂)) ⇾ (δ ⊢ (stack ∷ (◌ ⊕₁ e₂)) ↑ e₁)
  step-Let       : ∀ {stack : Stack Answer T₂}
                   → (δ ⊢ stack ↑ (Let e₁ In e₂)) ⇾ (δ ⊢ (stack ∷ (Let₁ ◌ In e₂)) ↑ e₁)
\end{code}

Transitive, reflexive closure of the step relation
\begin{code}
data _⇾⃰_ : State T → State T → Set where
  base  : ∀ {s : State T}        → s ⇾⃰ s
  step  : ∀ {s₁ s₂ s₃ : State T} → s₁ ⇾ s₂ → s₂ ⇾⃰ s₃ → s₁ ⇾⃰ s₃

⇾⃰-reflexive : ∀ {s : State Answer} → s ⇾⃰ s
⇾⃰-reflexive = base

⇾⃰-transitive : ∀ {s₀ s₁ s₂ : State Answer} → s₀ ⇾⃰ s₁ → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₂
⇾⃰-transitive (base)      q = q
⇾⃰-transitive (step s p)  q = step s (⇾⃰-transitive p q)
\end{code}

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

\begin{code}
infix  0 proof_
infixr 1 ⇾-link ⇾⃰-link
infix  2 _∎

proof_ : {s₁ s₂ : State Answer} → s₁ ⇾⃰ s₂ → s₁ ⇾⃰ s₂
proof s₁⇾⃰s₂ = s₁⇾⃰s₂

syntax ⇾-link x q p = x ⇾⟨ p ⟩ q
⇾-link : (s₀ : State Answer) {s₁ s₂ : State Answer} → s₁ ⇾⃰ s₂ → s₀ ⇾ s₁ → s₀ ⇾⃰ s₂
⇾-link _ q p = step p q

syntax ⇾⃰-link x q p = x ⇾⃰⟨ p ⟩ q
⇾⃰-link : (s₀ : State Answer) {s₁ s₂ : State Answer} → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₁ → s₀ ⇾⃰ s₂
⇾⃰-link _ q p = ⇾⃰-transitive p q

_∎ : (s : State Answer) → s ⇾⃰ s
e ∎ = ⇾⃰-reflexive
\end{code}


Trivial proof of correctness
\begin{code}
correct : ∀ (e : Γ ⊢ T) → (v : Value T) → (p : δ ⊢ e ⇓ v) →
  (δ ⊢ [] ↑ e) ⇾⃰ (δ ⊢ [] ↓ p) → δ ⊢ e ⇓ v
correct _ _ p _ = p
\end{code}

Completeness
\begin{code}
complete : ∀ (δ : Environment Γ) (stack : Stack Answer T) (e : Γ ⊢ T) (v : Value T) →
  (p : δ ⊢ e ⇓ v) → (δ ⊢ stack ↑ e) ⇾⃰ (δ ⊢ stack ↓ p)
complete {Γ = Γ} δ stack (Num x) _ (NUM .x) = step step-Num base
complete δ stack True _ TRUE        = step step-True base
complete δ stack False _ FALSE      = step step-False base
complete δ stack (Var e) v (VAR p) = step step-Var base
complete δ stack (If e₁ Then e₂ Else e₃) v (IF₁ p₁ p₂ .e₃) =
  proof
    (δ ⊢ stack ↑ If e₁ Then e₂ Else e₃)
  ⇾⟨ step-If {p₁ = p₁} ⟩
    (δ ⊢ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↑ e₁)
  ⇾⃰⟨ complete δ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) e₁ true p₁ ⟩
    (δ ⊢ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↓ p₁)
  ⇾⟨ step-If₁-true ⟩
    (δ ⊢ (stack ∷ (If₂ p₁ Then ◌ Else e₃)) ↑ e₂)
  ⇾⃰⟨ complete δ (stack ∷ (If₂ p₁ Then ◌ Else e₃)) e₂ v p₂ ⟩
    (δ ⊢ (stack ∷ (If₂ p₁ Then ◌ Else e₃)) ↓ p₂)
  ⇾⟨ step-If₂ ⟩
    (δ ⊢ stack ↓ IF₁ p₁ p₂ e₃)
  ∎
complete δ stack (If e₁ Then e₂ Else e₃) v (IF₂ p₁ .e₂ p₃) = 
  proof
    (δ ⊢ stack ↑ If e₁ Then e₂ Else e₃)
  ⇾⟨ step-If {p₁ = p₁} ⟩
    (δ ⊢ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↑ e₁)
  ⇾⃰⟨ complete δ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) e₁ false p₁ ⟩
    (δ ⊢ (stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↓ p₁)
  ⇾⟨ step-If₁-false ⟩
   (δ ⊢ (stack ∷ (If₃ p₁ Then e₂ Else ◌)) ↑ e₃)
  ⇾⃰⟨ complete δ (stack ∷ (If₃ p₁ Then e₂ Else ◌)) e₃ v p₃ ⟩
    (δ ⊢ (stack ∷ (If₃ p₁ Then e₂ Else ◌)) ↓ p₃)
  ⇾⟨ step-If₃ ⟩
    (δ ⊢ stack ↓ IF₂ p₁ e₂ p₃)
  ∎
complete δ stack (e₁ ⊕ e₂) v (ADD p₁ p₂) =
  proof
    (δ ⊢ stack ↑ (e₁ ⊕ e₂))
  ⇾⟨ step-⊕ ⟩
    (δ ⊢ (stack ∷ (◌ ⊕₁ e₂)) ↑ e₁)
  ⇾⃰⟨ complete δ (stack ∷ (◌ ⊕₁ e₂)) e₁ _ p₁ ⟩
    (δ ⊢ (stack ∷ (◌ ⊕₁ e₂)) ↓ p₁)
  ⇾⟨ step-⊕₁ ⟩
    (δ ⊢ (stack ∷ (p₁ ⊕₂ ◌)) ↑ e₂)
  ⇾⃰⟨ complete δ (stack ∷ (p₁ ⊕₂ ◌)) e₂ _ p₂ ⟩
    (δ ⊢ (stack ∷ (p₁ ⊕₂ ◌)) ↓ p₂)
  ⇾⟨ step-⊕₂ ⟩
    (δ ⊢ stack ↓ ADD p₁ p₂)
  ∎
complete δ stack (Let e₁ In e₂) v (LET {v₁ = v₁} p₁ p₂) =
  proof
    (δ ⊢ stack ↑ (Let e₁ In e₂))
  ⇾⟨ step-Let ⟩
    (δ ⊢ (stack ∷ (Let₁ ◌ In e₂)) ↑ e₁)
  ⇾⃰⟨ complete δ (stack ∷ (Let₁ ◌ In e₂)) e₁ _ p₁ ⟩
    (δ ⊢ (stack ∷ (Let₁ ◌ In e₂)) ↓ p₁)
  ⇾⟨ step-Let₁ ⟩
    ((δ , v₁) ⊢ (stack ∷ (Let₂ p₁ In ◌)) ↑ e₂)
  ⇾⃰⟨ complete (δ , v₁) (stack ∷ (Let₂ p₁ In ◌)) e₂ _ p₂ ⟩
    ((δ , v₁) ⊢ (stack ∷ (Let₂ p₁ In ◌)) ↓ p₂)
  ⇾⟨ step-Let₂ ⟩
    (δ ⊢ stack ↓ LET p₁ p₂)
  ∎
\end{code}
