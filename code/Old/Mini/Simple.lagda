--------------------------------------------------------------------------------
-- A simple language that only has simple constructs and no branching
--------------------------------------------------------------------------------

\begin{code}
module Simple where

open import Data.Bool renaming (Bool to 𝔹) using ()
open import Data.Nat using (ℕ)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
\end{code}

--------------------------------------------------------------------------------
-- Defining the source language
--------------------------------------------------------------------------------

We only have Bools and Nats as types in this language
\begin{code}
data Type : Set where
  Bool : Type
  Nat  : Type
  _⇒_  : Type → Type → Type
\end{code}

\begin{code}
open import Context Type

private variable
  Γ Δ : Context
  T T₁ T₂ Answer : Type
\end{code}

Curch-style syntax where each expression is given a type
\begin{code}
data _⊢_ : Context → Type → Set where
  Num          : ℕ → Γ ⊢ Nat
  True         : Γ ⊢ Bool
  False        : Γ ⊢ Bool
  Var          : T ∈ Γ → Γ ⊢ T
  _⊕_          : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Nat
  _⋏_          : Γ ⊢ Bool → Γ ⊢ Bool → Γ ⊢ Bool
  _≈_          : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Bool
  Let_In_      : Γ ⊢ T₁ → (Γ , T₁) ⊢ T₂ → Γ ⊢ T₂
  ƛ_           : (Γ , T₁) ⊢ T₂ → Γ ⊢ (T₁ ⇒ T₂)
  _·_          : Γ ⊢ (T₁ ⇒ T₂) → Γ ⊢ T₁ → Γ ⊢ T₂
\end{code}

Values are indexed by their type and carry Agda expressions
\begin{code}
mutual 
  data Value : Type → Set where
    Nat  : ℕ → Value Nat
    Bool : 𝔹 → Value Bool
    Closure : Environment Γ → (Γ , T₁) ⊢ T₂ → Value (T₁ ⇒ T₂)

  open import Environment Type Value
\end{code}

\begin{code}
private variable
  δ  : Environment Γ
  δ' : Environment Δ
\end{code}


\begin{code}
private variable
  e e₁ e₂ e₃ : Γ ⊢ T
  v v₁ v₂ : Value T
  n n₁ n₂ : Value Nat
  b b₁ b₂ : Value Bool
\end{code}

Some helper definitions
\begin{code}
true : Value Bool
true = (Bool Data.Bool.true)

false : Value Bool
false = (Bool Data.Bool.false)

_+_ : Value Nat → Value Nat → Value Nat
Nat a + Nat b = Nat (a Data.Nat.+ b)

_∧_ : Value Bool → Value Bool → Value Bool
Bool a ∧ Bool b = Bool (a Data.Bool.∧ b)

_=?_ : Value Nat → Value Nat → Value Bool
Nat a =? Nat b = Bool (a Data.Nat.≡ᵇ b)
\end{code}

Big-step semantics where an expression is related to the value it evaluates to
\begin{code}
data _⊢_⇓_ : Environment Γ → Γ ⊢ T → Value T → Set where
  NUM   : ∀ n → δ ⊢ (Num n) ⇓ (Nat n)
  TRUE  : δ ⊢ True ⇓ true
  FALSE : δ ⊢ False ⇓ false
  FUN   : ∀ (f : (Γ , T₁) ⊢ T₂) → δ ⊢ ƛ f ⇓ Closure δ f
  VAR   : ∀ (v : T ∈ Γ) → δ ⊢ (Var v) ⇓ lookupₑ δ v
  ADD   : δ ⊢ e₁ ⇓ n₁ → δ ⊢ e₂ ⇓ n₂ → δ ⊢ (e₁ ⊕ e₂) ⇓ (n₁ + n₂)
  AND   : δ ⊢ e₁ ⇓ b₁ → δ ⊢ e₂ ⇓ b₂ → δ ⊢ (e₁ ⋏ e₂) ⇓ (b₁ ∧ b₂)
  EQUAL : δ ⊢ e₁ ⇓ n₁ → δ ⊢ e₂ ⇓ n₂ → δ ⊢ (e₁ ≈ e₂) ⇓ (n₁ =? n₂)
  LET   : δ ⊢ e₁ ⇓ v₁ → (δ , v₁) ⊢ e₂ ⇓ v → δ ⊢ Let e₁ In e₂ ⇓ v
  APP   : ∀ {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {e₂ : Γ ⊢ T₁} {f : (Γ , T₁) ⊢ T₂}
          → δ ⊢ e₁ ⇓ Closure δ' f → δ ⊢ e₂ ⇓ v₂ → (δ' , v₂) ⊢ f ⇓ v → δ ⊢ e₁ · e₂ ⇓ v
\end{code}

--------------------------------------------------------------------------------
-- Machine definition
--------------------------------------------------------------------------------

A hole is just a placeholder for some value that is currently being evaluated
\begin{code}
data Hole : Set where
  ◌ : Hole
\end{code}

Stack frames with explicit holes.
If an expression 𝑒 has 𝑛 subexpressions then 𝑒 will have 𝑛 stack frames.
The type Frame is indexed by two types: first the overall type of the expression
and second the type of the hole.
\begin{code}
data Frame : Type → Type → Set where
  _⊕₁_     : Hole → Γ ⊢ Nat → Frame Nat Nat
  _⊕₂_     : δ ⊢ e ⇓ n → Hole → Frame Nat Nat
  _⋏₁_     : Hole → Γ ⊢ Bool → Frame Bool Bool
  _⋏₂_     : δ ⊢ e ⇓ b → Hole → Frame Bool Bool
  _≈₁_     : Hole → Γ ⊢ Nat → Frame Bool Nat
  _≈₂_     : δ ⊢ e ⇓ n → Hole → Frame Bool Nat
  Let₁_In_ : Hole → (Γ , T₁) ⊢ T₂ → Frame T₂ T₁
  Let₂_In_ : δ ⊢ e ⇓ v → Hole → Frame T₂ T₂
  _·₁_     : Hole → Γ ⊢ T₁ → Frame T₂ (T₁ ⇒ T₂)
  _·₂_     : δ ⊢ e ⇓ v → Hole → Frame T₂ T₁
\end{code}

A standard stack definition with the addition that we keep track of the
expressions type and the type of the hole in the top-most frame.
This keeps track of the invariant that types are preserved.
\begin{code}
data Stack (Answer : Type) : Type → Set where
  []  : Stack Answer Answer
  _∷_ : Stack Answer T₁ → Frame T₁ T₂ → Stack Answer T₂
\end{code}

Machine state
Going up the tree, aka. eval: ↑
Going down the tree, aka. return: ↓
When adding variables, the state also needs to track the current value of
a variable. Thus, we add the environment to both state constructors.
\begin{code}
data State (Answer : Type) : Set where
  _⊢_↓_ : (δ : Environment Γ) → Stack Answer T → {e : Γ ⊢ T} → δ ⊢ e ⇓ v → State Answer
  _⊢_↑_ : (δ : Environment Γ) → Stack Answer T → Γ ⊢ T → State Answer
\end{code}

Step relation
We obtain the different constructors from looking at the evaluation rules.
For example, if the top-most stack frame is (◌ ⊕₁ e₂) and have a proof p₁ to what
the left argument evaluates, then we replace it with a new frame (p₁ ⊕₂ ◌) and
start evaluating e₂.
\begin{code}
data _⇾_ : State T → State T → Set where
  step-⊕₁        : ∀ {e₁ e₂ : Γ ⊢ Nat} {p₁ : δ ⊢ e₁ ⇓ n₁} {stack : Stack Answer Nat}
                   → (δ ⊢ (stack ∷ (◌ ⊕₁ e₂)) ↓ p₁) ⇾ (δ ⊢ (stack ∷ (p₁ ⊕₂ ◌)) ↑ e₂)
  step-⊕₂        : ∀ {e₁ e₂ : Γ ⊢ Nat} {p₁ : δ ⊢ e₁ ⇓ n₁} {p₂ : δ ⊢ e₂ ⇓ n₂} {stack : Stack Answer Nat}
                   → (δ ⊢ (stack ∷ (p₁ ⊕₂ ◌)) ↓ p₂) ⇾ (δ ⊢ stack ↓ ADD p₁ p₂)
  step-⋏₁        : ∀ {e₁ e₂ : Γ ⊢ Bool} {p₁ : δ ⊢ e₁ ⇓ b₁} {stack : Stack Answer Bool}
                   → (δ ⊢ (stack ∷ (◌ ⋏₁ e₂)) ↓ p₁) ⇾ (δ ⊢ (stack ∷ (p₁ ⋏₂ ◌)) ↑ e₂)
  step-⋏₂        : ∀ {e₁ e₂ : Γ ⊢ Bool} {p₁ : δ ⊢ e₁ ⇓ b₁} {p₂ : δ ⊢ e₂ ⇓ b₂} {stack : Stack Answer Bool}
                   → (δ ⊢ (stack ∷ (p₁ ⋏₂ ◌)) ↓ p₂) ⇾ (δ ⊢ stack ↓ AND p₁ p₂)
  step-≈₁        : ∀ {e₁ e₂ : Γ ⊢ Nat} {p₁ : δ ⊢ e₁ ⇓ n₁} {stack : Stack Answer Bool}
                   → (δ ⊢ (stack ∷ (◌ ≈₁ e₂)) ↓ p₁) ⇾ (δ ⊢ (stack ∷ (p₁ ≈₂ ◌)) ↑ e₂)
  step-≈₂        : ∀ {e₁ e₂ : Γ ⊢ Nat} {p₁ : δ ⊢ e₁ ⇓ n₁} {p₂ : δ ⊢ e₂ ⇓ n₂} {stack : Stack Answer Bool}
                   → (δ ⊢ (stack ∷ (p₁ ≈₂ ◌)) ↓ p₂) ⇾ (δ ⊢ stack ↓ EQUAL p₁ p₂)
  step-Let₁      : ∀ {e₁ : Γ ⊢ T₁} {e₂ : (Γ , T₁) ⊢ T₂} {p₁ : δ ⊢ e₁ ⇓ v₁} {stack : Stack Answer T₂}
                   → (δ ⊢ stack ∷ (Let₁ ◌ In e₂) ↓ p₁) ⇾ ((δ , v₁) ⊢ stack ∷ (Let₂ p₁ In ◌) ↑ e₂)
  step-Let₂      : ∀ {e₁ : Γ ⊢ T₁} {e₂ : (Γ , T₁) ⊢ T₂} {p₁ : δ ⊢ e₁ ⇓ v₁} {p₂ : (δ , v₁) ⊢ e₂ ⇓ v₂}
                     {stack : Stack Answer T₂}
                   → ((δ , v₁) ⊢ stack ∷ (Let₂ p₁ In ◌) ↓ p₂) ⇾ (δ ⊢ stack ↓ LET p₁ p₂)
  step-·₁        : ∀ {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {e₂ : Γ ⊢ T₁} {p₁ : δ ⊢ e₁ ⇓ v₁} {stack : Stack Answer T₂}
                   → (δ ⊢ stack ∷ (◌ ·₁ e₂) ↓ p₁) ⇾ (δ ⊢ stack ∷ (p₁ ·₂ ◌) ↑ e₂)
  step-·₂        : ∀ {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {e₂ : Γ ⊢ T₁} {f : (Γ , T₁) ⊢ T₂} {v : Value T₂} {p₁ : δ ⊢ e₁ ⇓ (Closure δ' f)}
                     {p₂ : δ ⊢ e₂ ⇓ v₂} {p₃ : (δ' , v₂) ⊢ f ⇓ v} {stack : Stack Answer T₂}
                   → (δ ⊢ stack ∷ (p₁ ·₂ ◌) ↓ p₂) ⇾ (δ ⊢ stack ↓ APP p₁ p₂ p₃)

  step-True      : ∀ {stack : Stack Answer Bool}
                   → (δ ⊢ stack ↑ True) ⇾ (δ ⊢ stack ↓ TRUE)
  step-False     : ∀ {stack : Stack Answer Bool}
                   → (δ ⊢ stack ↑ False) ⇾ (δ ⊢ stack ↓ FALSE)
  step-Num       : ∀ {n : ℕ} {stack : Stack Answer Nat}
                   → (δ ⊢ stack ↑ Num n) ⇾ (δ ⊢ stack ↓ NUM n)
  step-Var       : ∀ {v : T ∈ Γ} {stack : Stack Answer T} 
                   → (δ ⊢ stack ↑ Var v) ⇾ (δ ⊢ stack ↓ VAR v)
  step-ƛ         : ∀ {Γ : Context} {δ : Environment Γ} {T₁ T₂ : Type} {f : (Γ , T₁) ⊢ T₂} {stack : Stack Answer (T₁ ⇒ T₂)}
                   → (δ ⊢ stack ↑ (ƛ f)) ⇾ (δ ⊢ stack ↓ FUN f)
  step-⊕         : ∀ {e₁ e₂ : Γ ⊢ Nat} {stack : Stack Answer Nat}
                   → (δ ⊢ stack ↑ (e₁ ⊕ e₂)) ⇾ (δ ⊢ (stack ∷ (◌ ⊕₁ e₂)) ↑ e₁)
  step-⋏         : ∀ {e₁ e₂ : Γ ⊢ Bool} {stack : Stack Answer Bool}
                   → (δ ⊢ stack ↑ (e₁ ⋏ e₂)) ⇾ (δ ⊢ (stack ∷ (◌ ⋏₁ e₂)) ↑ e₁)
  step-≈         : ∀ {e₁ e₂ : Γ ⊢ Nat} {stack : Stack Answer Bool}
                   → (δ ⊢ stack ↑ (e₁ ≈ e₂)) ⇾ (δ ⊢ (stack ∷ (◌ ≈₁ e₂)) ↑ e₁)
  step-Let       : ∀ {e₁ : Γ ⊢ T₁} {e₂ : (Γ , T₁) ⊢ T₂} {stack : Stack Answer T₂} 
                   → (δ ⊢ stack ↑ (Let e₁ In e₂)) ⇾ (δ ⊢ (stack ∷ (Let₁ ◌ In e₂)) ↑ e₁)
  step-·         : ∀ {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {e₂ : Γ ⊢ T₁} {stack : Stack Answer T₂} 
                   → (δ ⊢ stack ↑ (e₁ · e₂)) ⇾ (δ ⊢ stack ∷ (◌ ·₁ e₂) ↑ e₁)
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
complete δ stack (Num x) _ (NUM .x) = step step-Num base
complete δ stack True _ TRUE        = step step-True base
complete δ stack False _ FALSE      = step step-False base
complete δ stack (Var e) v (VAR p)  = step step-Var base
complete δ stack (ƛ f) v (FUN p)  = step step-ƛ base
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
complete δ stack (e₁ ⋏ e₂) v (AND p₁ p₂) =
  proof
    (δ ⊢ stack ↑ (e₁ ⋏ e₂))
  ⇾⟨ step-⋏ ⟩
    (δ ⊢ (stack ∷ (◌ ⋏₁ e₂)) ↑ e₁)
  ⇾⃰⟨ complete δ (stack ∷ (◌ ⋏₁ e₂)) e₁ _ p₁ ⟩
    (δ ⊢ (stack ∷ (◌ ⋏₁ e₂)) ↓ p₁)
  ⇾⟨ step-⋏₁ ⟩
    (δ ⊢ (stack ∷ (p₁ ⋏₂ ◌)) ↑ e₂)
  ⇾⃰⟨ complete δ (stack ∷ (p₁ ⋏₂ ◌)) e₂ _ p₂ ⟩
    (δ ⊢ (stack ∷ (p₁ ⋏₂ ◌)) ↓ p₂)
  ⇾⟨ step-⋏₂ ⟩
    (δ ⊢ stack ↓ AND p₁ p₂)
  ∎
complete δ stack (e₁ ≈ e₂) v (EQUAL p₁ p₂) =
  proof
    (δ ⊢ stack ↑ (e₁ ≈ e₂))
  ⇾⟨ step-≈ ⟩
    (δ ⊢ (stack ∷ (◌ ≈₁ e₂)) ↑ e₁)
  ⇾⃰⟨ complete δ (stack ∷ (◌ ≈₁ e₂)) e₁ _ p₁ ⟩
    (δ ⊢ (stack ∷ (◌ ≈₁ e₂)) ↓ p₁)
  ⇾⟨ step-≈₁ ⟩
    (δ ⊢ (stack ∷ (p₁ ≈₂ ◌)) ↑ e₂)
  ⇾⃰⟨ complete δ (stack ∷ (p₁ ≈₂ ◌)) e₂ _ p₂ ⟩
    (δ ⊢ (stack ∷ (p₁ ≈₂ ◌)) ↓ p₂)
  ⇾⟨ step-≈₂ ⟩
    (δ ⊢ stack ↓ EQUAL p₁ p₂)
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
complete δ stack (e₁ · e₂) v (APP p₁ p₂ p₃) =
  proof
    (δ ⊢ stack ↑ (e₁ · e₂))
  ⇾⟨ step-· ⟩
    (δ ⊢ (stack ∷ (◌ ·₁ e₂)) ↑ e₁)
  ⇾⃰⟨ complete δ (stack ∷ (◌ ·₁ e₂)) e₁ _ p₁ ⟩
    (δ ⊢ (stack ∷ (◌ ·₁ e₂)) ↓ p₁)
  ⇾⟨ step-·₁ ⟩
    (δ ⊢ (stack ∷ (p₁ ·₂ ◌)) ↑ e₂)
  ⇾⃰⟨ complete δ (stack ∷ (p₁ ·₂ ◌)) e₂ _ p₂ ⟩
    (δ ⊢ (stack ∷ (p₁ ·₂ ◌)) ↓ p₂)
  ⇾⟨ step-·₂ ⟩
    (δ ⊢ stack ↓ APP p₁ p₂ p₃)
  ∎
\end{code}
