--------------------------------------------------------------------------------
-- This is the new approach where the step function is now a relation between
-- states and states carry proof trees about their values.
-- The languages used in this example is very minimal, only consisting of
-- natural numbers, booleans and some operations.
--------------------------------------------------------------------------------

\begin{code}
module Mini where

open import Data.Bool renaming (Bool to 𝔹) using ()
open import Data.Nat using (ℕ)
\end{code}

--------------------------------------------------------------------------------
-- Defining the source language
--------------------------------------------------------------------------------

We only have Bools and Nats as types in this language
\begin{code}
data Type : Set where
  Bool : Type
  Nat  : Type
\end{code}

Values are indexed by their type and carry Agda expressions
\begin{code}
data Value : Type → Set where
  Nat  : ℕ → Value Nat
  Bool : 𝔹 → Value Bool
\end{code}

\begin{code}
private variable
  T T₁ T₂ Answer : Type
\end{code}

Curch-style syntax where each expression is given a type
\begin{code}
data ⊢_ : Type → Set where
  Num          : ℕ → ⊢ Nat
  True         : ⊢ Bool
  False        : ⊢ Bool
  If_Then_Else : ⊢ Bool → ⊢ T → ⊢ T → ⊢ T
  _⊕_          : ⊢ Nat → ⊢ Nat → ⊢ Nat
\end{code}

\begin{code}
private variable
  e e₁ e₂ e₃ : ⊢ T
  v : Value T
  n n₁ n₂ : Value Nat
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

Big-step semantics where an expression is related to the value it evaluates to
\begin{code}
data _⇓_ : ⊢ T → Value T → Set where
  NUM   : ∀ n → (Num n) ⇓ (Nat n)
  TRUE  : True ⇓ true
  FALSE : False ⇓ false
  IF₁   : e₁ ⇓ true → e₂ ⇓ v → (e₃ : ⊢ T) → If e₁ Then e₂ Else e₃ ⇓ v
  IF₂   : e₁ ⇓ false → (e₂ : ⊢ T) → e₃ ⇓ v → If e₁ Then e₂ Else e₃ ⇓ v
  ADD   : e₁ ⇓ n₁ → e₂ ⇓ n₂ → (e₁ ⊕ e₂) ⇓ (n₁ + n₂)
\end{code}

--------------------------------------------------------------------------------
-- Machine definition
--------------------------------------------------------------------------------

A hole is just a placeholder for some value
\begin{code}
data Hole : Set where
  ◌ : Hole
\end{code}

Stack frames with explicit holes.
\begin{code}
data Frame : Type → Type → Set where
  If₁_Then_Else_ : Hole → ⊢ T → ⊢ T → Frame T Bool
  If₂_Then_Else_ : e ⇓ true → Hole → ⊢ T → Frame T T
  If₃_Then_Else_ : e ⇓ false → ⊢ T → Hole → Frame T T
  _⊕₁_           : Hole → ⊢ Nat → Frame Nat Nat
  _⊕₂_           : e ⇓ n → Hole → Frame Nat Nat
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
\begin{code}
data State (Answer : Type) : Set where
  _↓_ : Stack Answer T → {e : ⊢ T} → e ⇓ v → State Answer
  _↑_ : Stack Answer T → ⊢ T → State Answer
\end{code}

Step relation
\begin{code}
data _⇾_ : State T → State T → Set where
  step-If₁-true  : ∀ {e₁ : ⊢ Bool} {e₂ e₃ : ⊢ T} {p₁ : e₁ ⇓ true} {stack : Stack Answer T}
                   → ((stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↓ p₁) ⇾ ((stack ∷ (If₂ p₁ Then ◌ Else e₃)) ↑ e₂)
  step-If₁-false : ∀ {e₁ : ⊢ Bool} {e₂ e₃ : ⊢ T} {p₁ : e₁ ⇓ false} {stack : Stack Answer T}
                   → ((stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↓ p₁) ⇾ ((stack ∷ (If₃ p₁ Then e₂ Else ◌)) ↑ e₃)
  step-If₂       : ∀ {e₁ : ⊢ Bool} {e₂ e₃ : ⊢ T} {p₁ : e₁ ⇓ true} {p₂ : e₂ ⇓ v} {stack : Stack Answer T}
                   → ((stack ∷ (If₂ p₁ Then ◌ Else e₃)) ↓ p₂) ⇾ (stack ↓ IF₁ p₁ p₂ e₃)
  step-If₃       : ∀ {e₁ : ⊢ Bool} {e₂ e₃ : ⊢ T} {p₁ : e₁ ⇓ false} {p₃ : e₃ ⇓ v} {stack : Stack Answer T}
                   → ((stack ∷ (If₃ p₁ Then e₂ Else ◌)) ↓ p₃) ⇾ (stack ↓ IF₂ p₁ e₂ p₃)
  step-⊕₁        : ∀ {e₁ e₂ : ⊢ Nat} {p₁ : e₁ ⇓ n₁} {stack : Stack Answer Nat}
                   → ((stack ∷ (◌ ⊕₁ e₂)) ↓ p₁) ⇾ ((stack ∷ (p₁ ⊕₂ ◌)) ↑ e₂)
  step-⊕₂        : ∀ {e₁ e₂ : ⊢ Nat} {p₁ : e₁ ⇓ n₁} {p₂ : e₂ ⇓ n₂} {stack : Stack Answer Nat}
                   → ((stack ∷ (p₁ ⊕₂ ◌)) ↓ p₂) ⇾ (stack ↓ ADD p₁ p₂)

  step-True      : ∀ {stack : Stack Answer Bool}
                   → (stack ↑ True) ⇾ (stack ↓ TRUE)
  step-False     : ∀ {stack : Stack Answer Bool}
                   → (stack ↑ False) ⇾ (stack ↓ FALSE)
  step-Num       : ∀ {n : ℕ} {stack : Stack Answer Nat}
                   → (stack ↑ Num n) ⇾ (stack ↓ NUM n)
  step-If        : ∀ {e₁ : ⊢ Bool} {e₂ e₃ : ⊢ T} {p₁ : e₁ ⇓ v} {stack : Stack Answer T}
                   → (stack ↑ If e₁ Then e₂ Else e₃) ⇾ ((stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↑ e₁)
  step-⊕         : ∀ {e₁ e₂ : ⊢ Nat} {stack : Stack Answer Nat}
                   → (stack ↑ (e₁ ⊕ e₂)) ⇾ ((stack ∷ (◌ ⊕₁ e₂)) ↑ e₁)
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
correct : ∀ (e : ⊢ T) → (v : Value T) → (p : e ⇓ v) →
  ([] ↑ e) ⇾⃰ ([] ↓ p) → e ⇓ v
correct _ _ p _ = p
\end{code}

Completeness
\begin{code}
complete : ∀ (stack : Stack Answer T) (e : ⊢ T) (v : Value T) →
  (p : e ⇓ v) → (stack ↑ e) ⇾⃰ (stack ↓ p)
complete stack (Num x) _ (NUM .x) = step step-Num base
complete stack True _ TRUE        = step step-True base
complete stack False _ FALSE      = step step-False base
complete stack (If e₁ Then e₂ Else e₃) v (IF₁ p₁ p₂ .e₃) =
  proof
    (stack ↑ If e₁ Then e₂ Else e₃)
  ⇾⟨ step-If {p₁ = p₁} ⟩
    ((stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↑ e₁)
  ⇾⃰⟨ complete (stack ∷ (If₁ ◌ Then e₂ Else e₃)) e₁ true p₁ ⟩
    ((stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↓ p₁)
  ⇾⟨ step-If₁-true ⟩
    ((stack ∷ (If₂ p₁ Then ◌ Else e₃)) ↑ e₂)
  ⇾⃰⟨ complete (stack ∷ (If₂ p₁ Then ◌ Else e₃)) e₂ v p₂ ⟩
    ((stack ∷ (If₂ p₁ Then ◌ Else e₃)) ↓ p₂)
  ⇾⟨ step-If₂ ⟩
    (stack ↓ IF₁ p₁ p₂ e₃)
  ∎
complete stack (If e₁ Then e₂ Else e₃) v (IF₂ p₁ .e₂ p₃) = 
  proof
    (stack ↑ If e₁ Then e₂ Else e₃)
  ⇾⟨ step-If {p₁ = p₁} ⟩
    ((stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↑ e₁)
  ⇾⃰⟨ complete (stack ∷ (If₁ ◌ Then e₂ Else e₃)) e₁ false p₁ ⟩
    ((stack ∷ (If₁ ◌ Then e₂ Else e₃)) ↓ p₁)
  ⇾⟨ step-If₁-false ⟩
   ((stack ∷ (If₃ p₁ Then e₂ Else ◌)) ↑ e₃)
  ⇾⃰⟨ complete (stack ∷ (If₃ p₁ Then e₂ Else ◌)) e₃ v p₃ ⟩
    ((stack ∷ (If₃ p₁ Then e₂ Else ◌)) ↓ p₃)
  ⇾⟨ step-If₃ ⟩
    (stack ↓ IF₂ p₁ e₂ p₃)
  ∎
complete stack (e₁ ⊕ e₂) v (ADD p₁ p₂) =
  proof
    (stack ↑ (e₁ ⊕ e₂))
  ⇾⟨ step-⊕ ⟩
    ((stack ∷ (◌ ⊕₁ e₂)) ↑ e₁)
  ⇾⃰⟨ complete (stack ∷ (◌ ⊕₁ e₂)) e₁ _ p₁ ⟩
    ((stack ∷ (◌ ⊕₁ e₂)) ↓ p₁)
  ⇾⟨ step-⊕₁ ⟩
    ((stack ∷ (p₁ ⊕₂ ◌)) ↑ e₂)
  ⇾⃰⟨ complete (stack ∷ (p₁ ⊕₂ ◌)) e₂ _ p₂ ⟩
    ((stack ∷ (p₁ ⊕₂ ◌)) ↓ p₂)
  ⇾⟨ step-⊕₂ ⟩
    (stack ↓ ADD p₁ p₂)
  ∎
\end{code}
