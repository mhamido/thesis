Mini2, a minuscule subset of F# featuring exceptions.

%------------------------------------------------------------------------------

\begin{code}
module STLC.Mini2 where

open import Data.Empty using (⊥) renaming (⊥-elim to ex-falso)
open import Data.Bool renaming (Bool to 𝔹) hiding (T)
open import Relation.Binary.PropositionalEquality.Core using (_≡_) renaming (refl to reflexive)
open import Data.Nat renaming (_+_ to infixl 46 _+_; suc to succ)
open import Data.Product using (∃) renaming (_,_ to _﹐_)
open import Data.Sum using (_⊎_) renaming (inj₁ to ok; inj₂ to err)
\end{code}

\begin{code}
infix  149 `_
infixl 146 _⊞_
infix  120 𝚒𝚏_𝚝𝚑𝚎𝚗_𝚎𝚕𝚜𝚎_
infix  110 _⊢_
infixr  20 _⇒_

infixl 146 _⊞₀_ _⊞₁_
infix  120 _𝚎𝚕𝚜𝚎_
infixr  35 _∷_
infix   30 _⊢_↓_ _⊢_↑_
\end{code}

%------------------------------------------------------------------------------

Representing types.

<<types>>
\begin{code}
data Type : Set where
  𝙱𝚘𝚘𝚕 : Type
  𝙽𝚊𝚝  : Type
  _⇒_  : Type → Type → Type

test : ℕ → 𝔹
test zero = true
test (succ n) = false
\end{code}

Interpreting an expression type as an Agda type. The value of e : ⊢ A
is an element of ⊨ A.

\begin{code}
open import Context Type public

record Closure (T₂ T₂ : Type) : Set
data _⊢_ : Context → Type → Set

⊨ : Type → Set
⊨ 𝙱𝚘𝚘𝚕     = 𝔹
⊨ 𝙽𝚊𝚝      = ℕ
⊨ (a ⇒ b)  = Closure a b

open import Environment Type ⊨ public

record Closure T₁ T₂ where
  inductive 
  constructor ⟨_,_⟩
  field
    {Γᶜ} : Context
    δᶜ : Environment Γᶜ
    eᶜ : (Γᶜ , T₁) ⊢ T₂
\end{code}

\begin{code}
private variable
  A B T T₁ T₂ Answer : Type
  Γ Δ : Context
  δ : Environment Γ
\end{code}

%------------------------------------------------------------------------------

Static semantics (Church-style).

<<expressions>>
\begin{code}
data _⊢_ where
  `_ : ⊨ A → Γ ⊢ A
  _⊞_ : Γ ⊢ 𝙽𝚊𝚝 → Γ ⊢ 𝙽𝚊𝚝 → Γ ⊢ 𝙽𝚊𝚝
  𝚝𝚎𝚜𝚝 : Γ ⊢ 𝙽𝚊𝚝 → Γ ⊢ 𝙱𝚘𝚘𝚕
  𝚒𝚏_𝚝𝚑𝚎𝚗_𝚎𝚕𝚜𝚎_ : Γ ⊢ 𝙱𝚘𝚘𝚕 → Γ ⊢ A → Γ ⊢ A → Γ ⊢ A
  
  Var : A ∈ Γ → Γ ⊢ A
  _·_ : Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
  ƛ_  : (Γ , A) ⊢ B → Γ ⊢ (A ⇒ B)
  -- LetRec_       : (Γ , T₁ ⇒ T₂ , T₁) ⊢ T₂ → Γ ⊢ (T₁ ⇒ T₂)
infixl 10 _·_

private variable
  e e₁ e₂ e₃ : Γ ⊢ T
  v v₁ v₂ v₃ : ⊨ T
  n n₁ n₂ : ⊨ 𝙽𝚊𝚝

data _⊢_⇓_ : Environment Γ → Γ ⊢ A → ⊨ A → Set where
  `_ : (v : ⊨ A) → δ ⊢ ` v ⇓ v

  _⊞_ 
    : δ ⊢ e₁ ⇓ v₁
    → δ ⊢ e₂ ⇓ v₂
    ----------------------------
    → δ ⊢ (e₁ ⊞ e₂) ⇓ (v₁ + v₂)

  𝚝𝚎𝚜𝚝
    : ∀ {e : Γ ⊢ 𝙽𝚊𝚝} {n : ℕ}
    → δ ⊢ e ⇓ n
    ----------------------------
    → δ ⊢ (𝚝𝚎𝚜𝚝 e) ⇓ (test n)

  𝚒𝚏-𝚝𝚑𝚎𝚗 
    : (p₀ : δ ⊢ e₁ ⇓ true)
    → (p₁ : δ ⊢ e₂ ⇓ v₂)
    → (e₃ : Γ ⊢ A)
    ----------------------------
    → δ ⊢ (𝚒𝚏 e₁ 𝚝𝚑𝚎𝚗 e₂ 𝚎𝚕𝚜𝚎 e₃) ⇓ v₂

  𝚒𝚏-𝚎𝚕𝚜𝚎
    : (p₀ : δ ⊢ e₁ ⇓ false)
    → (e₂ : Γ ⊢ A)
    → (p₂ : δ ⊢ e₃ ⇓ v₃)
    ----------------------------
    → δ ⊢ (𝚒𝚏 e₁ 𝚝𝚑𝚎𝚗 e₂ 𝚎𝚕𝚜𝚎 e₃) ⇓ v₃

  var 
    : ∀ (v : A ∈ Γ)
    ---------------------------
    → δ ⊢ (Var v) ⇓ lookupₑ δ v

  fun : (e : (Γ , A) ⊢ B) 
      → δ ⊢ (ƛ e₁) ⇓ ⟨ δ , e₁ ⟩

  app 
    : ∀ {e₁ : Γ ⊢ (A ⇒ B)} {e₂ : Γ ⊢ A} 
      {Γᶜ} {δᶜ} {eᶜ : (Γᶜ , A) ⊢ B}
      {v₁ : _} {v₂ : _}
    → δ ⊢ e₁         ⇓ ⟨ δᶜ , eᶜ ⟩
    → δ ⊢ e₂         ⇓ v₁
    → (δᶜ , v₁) ⊢ eᶜ ⇓ v₂
    ---------------------
    → δ ⊢ (e₁ · e₂) ⇓ v₂
\end{code}

The first constructor embeds values into terms.

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

\begin{code}
data Hole : Set where
  ◌ : Hole
\end{code}

-------------------------------------------------------------------------------

A small-step machine.

\begin{code}
data Frame : Type → Type → Set where
  _𝚎𝚕𝚜𝚎_  : Γ ⊢ A → Γ ⊢ A → Frame A 𝙱𝚘𝚘𝚕
  _⊞₀_    : Hole → Γ ⊢ 𝙽𝚊𝚝 → Frame 𝙽𝚊𝚝 𝙽𝚊𝚝
  _⊞₁_    : ⊨ 𝙽𝚊𝚝 → Hole → Frame 𝙽𝚊𝚝 𝙽𝚊𝚝
  𝚝𝚎𝚜𝚝    : Hole → Frame 𝙱𝚘𝚘𝚕 𝙽𝚊𝚝
  
  app₁    : Hole 
          → Γ ⊢ A
          → Frame B (A ⇒ B)

  app₂    : ⊨ (A ⇒ B)
          → Hole 
          → Frame B A

  app₃    : ⊨ (A ⇒ B)
          → ⊨ A 
          → Hole
          → Frame B B

\end{code}

An element of type Frame A B is an “expression node” of type ⊢ A with a
hole of type ⊢ B.

\begin{code}
data Stack (Answer : Type) : Type → Set where
  []  : Stack Answer Answer
  _∷_ : Stack Answer A → Frame A B → Stack Answer B
\end{code}

A stack is a list of frames, sometimes called a zipper, a path into an
“expression tree”. An element of type Stack Answer A is an “expression
tree” of type ⊢ Answer with a hole of type ⊢ A.

The machine is in one of three modes:
●  _↑_: call mode (going up the tree), an expression is evaluated;
●  _↓_: return mode (going down the tree), a value is returned.

\begin{code}
data State (Answer : Type) : Set where
  _⊢_↑_ : (δ : Environment Γ) → Stack Answer A → Γ ⊢ A → State Answer
  _⊢_↓_ : (δ : Environment Γ) → Stack Answer A →   ⊨ A → State Answer
\end{code}

\begin{code}
private
  variable
    stack : Stack Answer A
\end{code}

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

NOTE: We cannot describe the step relation functionally. Both `Frame` and the Stack constructors bring in arbitrary contexts.
When modeling these as constructors in a datatype, this is dealt with via unification. 
If we fill a hole expecting a `Γ₁ ⊢ A` with an expression of type `Γ ⊢ A`, then the type checker adds a constraint `Γ ~ Γ₁`.
See [Simplified.lagda] for the relation described as a `data` type.

\begin{code} 
-- step : State Answer → State Answer
-- step (δ ⊢ stack ↑     ` x)             = δ ⊢ stack ↓ x
-- step (δ ⊢ stack ↑ e₁ ⊞ e₂)             = δ ⊢ stack ∷ ◌ ⊞₀ e₂ ↑ e₁
-- step (δ ⊢ stack ↑ 𝚝𝚎𝚜𝚝  e)             = δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e
-- step (δ ⊢ stack ↑ 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) = δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↑ e
-- step (δ ⊢ stack ↑               Var x) = δ ⊢ stack ↓ lookupₑ δ x
-- step (δ ⊢ stack ↑ (e₁ · e₂))           = δ ⊢ stack ∷ app₁ ◌ e₂ ↑ e₁
-- step (δ ⊢ stack ↑ (ƛ e))               = δ ⊢ stack ↓ ⟨ δ , e ⟩

-- step (δ ⊢ [] ↓ v) = δ ⊢ [] ↓ v
-- step (δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ v) = δ ⊢ stack ↑ (if v then e₁ else e₂)
-- step (δ ⊢ stack ∷ ◌ ⊞₀ e₂ ↓ v₁) = δ ⊢ stack ∷ v₁ ⊞₁ ◌ ↑ e₂
-- step (δ ⊢ stack ∷ v₁ ⊞₁ ◌ ↓ v₂) = δ ⊢ stack ↓ (v₁ + v₂)
-- step (δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ v) = δ ⊢ stack ↓ test v
-- step (δ ⊢ stack ∷ app₁ ◌ e₂ ↓ v₁) = δ ⊢ stack ∷ app₂ v₁ ◌ ↑ e₂
-- step (δ ⊢ stack ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌ ↓ v₂) = (δᶜ , v₂) ⊢ stack ∷ app₃ ⟨ δᶜ , eᶜ ⟩ v₂ ◌ ↑ eᶜ
-- step (δ ⊢ stack ∷ app₃ v₁ v₂ ◌ ↓ v₃) = δ ⊢ stack ↓ v₃
\end{code}

\begin{code}
-- steps : ℕ → State Answer → State Answer
-- steps (zero)   s = s
-- steps (succ n) s = step (steps n s)

deterministic : ∀ {T : Type} {e : Γ ⊢ T} {v₁ v₂ : ⊨ T} → δ ⊢ e ⇓ v₁ → δ ⊢ e ⇓ v₂ → v₁ ≡ v₂
deterministic (` _) (` _) = reflexive
deterministic (p₁ ⊞ p₂) (q₁ ⊞ q₂) with deterministic p₁ q₁ | deterministic p₂ q₂
... | reflexive | reflexive = reflexive
deterministic (𝚒𝚏-𝚝𝚑𝚎𝚗 p₁ p₂ e₃) (𝚒𝚏-𝚝𝚑𝚎𝚗 q₁ q₂ e₄) = deterministic p₂ q₂
deterministic (𝚒𝚏-𝚎𝚕𝚜𝚎 p₁ e₂ p₃) (𝚒𝚏-𝚎𝚕𝚜𝚎 q₁ e₃ q₃) = deterministic p₃ q₃
deterministic (𝚒𝚏-𝚝𝚑𝚎𝚗 p₁ p₂ e₃) (𝚒𝚏-𝚎𝚕𝚜𝚎 q₁ e₂ q₃) with deterministic p₁ q₁ 
... | ()
deterministic (𝚒𝚏-𝚎𝚕𝚜𝚎 p₁ e₂ p₃) (𝚒𝚏-𝚝𝚑𝚎𝚗 q₁ q₂ e₃) with deterministic p₁ q₁ 
... | ()
deterministic (𝚝𝚎𝚜𝚝 p) (𝚝𝚎𝚜𝚝 q) with deterministic p q
... | reflexive = reflexive

deterministic (var v) (var u) = reflexive
deterministic (fun e₁) (fun e₂) = reflexive
deterministic (app f₁ x₁ v₁) (app f₂ x₂ v₂) with deterministic f₁ f₂ | deterministic x₁ x₂
... | reflexive | reflexive = deterministic v₁ v₂

{-# TERMINATING #-} 
-- NOTE: We only need this because Agda's termination checker is not convinced that the call to
-- `total {δ = δᶜ , v₂} eᶜ` is smaller than `total (e₁ · e₂)`.

total : ∀ {T : Type} (e : Γ ⊢ T) → ∃ (λ v → δ ⊢ e ⇓ v)
total (` x) = x ﹐ ` x 

total (𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) with total e | total e₁ | total e₂
... | false ﹐ p₁ | _      | v ﹐ p₂ = v ﹐ 𝚒𝚏-𝚎𝚕𝚜𝚎 p₁ e₁ p₂
... | true  ﹐ p₁ | v ﹐ p₂ | _      = v ﹐ 𝚒𝚏-𝚝𝚑𝚎𝚗 p₁ p₂ e₂

total (e₁ ⊞ e₂) with total e₁ | total e₂
... | v₁ ﹐ p₁ | v₂ ﹐ p₂ = v₁ + v₂ ﹐ p₁ ⊞ p₂

total (𝚝𝚎𝚜𝚝 e) with total e
... | v ﹐ p = test v ﹐ 𝚝𝚎𝚜𝚝 p

total {δ = δ} (Var x) = lookupₑ δ x ﹐ var x
total {δ = δ} (ƛ e) = ⟨ δ , e ⟩ ﹐ fun e

total (e₁ · e₂) with total e₁ | total e₂ 
... | ⟨ δᶜ , eᶜ ⟩ ﹐ p₁ | v₂ ﹐ p₂ with total {δ = δᶜ , v₂} eᶜ
... | v₃ ﹐ p₃ = v₃ ﹐ app p₁ p₂ p₃
\end{code}


