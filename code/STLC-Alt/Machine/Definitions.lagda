A small-step machine for Mini.

correctness:   ([] ↑ e) ⇾⃰ ([] ↓ v)  →  e ⇓ v
completeness:  e ⇓ v  →  ([] ↑ e) ⇾⃰ ([] ↓ v)

%------------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module STLC-Alt.Machine.Definitions where

open import STLC-Alt.Mini2
  hiding (deterministic; Frame; Stack; State {- ; base; step -})
  renaming (total to ↓-total)
  public

open import Data.Bool hiding (T)
open import Data.Nat renaming (_+_ to infixl 46 _+_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_) renaming (refl to reflexive)
open import Relation.Nullary.Negation
open import Data.Product using (∃) renaming (_,_ to _﹐_)
open import Data.Empty using (⊥) renaming (⊥-elim to ex-falso-quodlibet)
\end{code}

\begin{code}
infixl 146 _⊞₀_ _⊞₁_
infix  120 _𝚎𝚕𝚜𝚎_
infixr  35 _∷_
infix   30 _⊢_↓_ _⊢_↑_
\end{code}

\begin{code}
private variable
  Γ Δ Δ′ : Context
  δ δ′ δᶜ : Environment Γ
  A B T Answer : Type
  
  n n₀ n₁ : ℕ
  v v₁ v₂ v₃ : ⊨ A
  e e₁ e₂ eᶜ : Γ ⊢ A 
  x : T ∈ Γ

\end{code}

-------------------------------------------------------------------------------

A small-step machine.

\begin{code}
data Frame : Context → Context → Type → Type → Set where
  _𝚎𝚕𝚜𝚎_  : Γ ⊢ A     → Γ ⊢ A   → Frame Γ Γ A Type.𝙱𝚘𝚘𝚕
  _⊞₀_    : Hole      → Γ ⊢ 𝙽𝚊𝚝 → Frame Γ Γ 𝙽𝚊𝚝 𝙽𝚊𝚝
  _⊞₁_    : ⊨ 𝙽𝚊𝚝     → Hole    → Frame Γ Γ 𝙽𝚊𝚝 𝙽𝚊𝚝
  𝚝𝚎𝚜𝚝    : Hole                → Frame Γ Γ 𝙱𝚘𝚘𝚕 𝙽𝚊𝚝
  app₁    : Hole      → Γ ⊢ A   → Frame Γ Γ B (A ⇒ B)
  app₂    : ⊨ (A ⇒ B) → Hole    → Frame Γ Γ B A
  -- app₃: outer context is Γ (with environment δ), we're evaluating closure body in (Δ , A)
  -- Notice how the closure is deconstructed here. 
  app₃    : Environment Γ → (δᶜ : Environment Δ) → ((Δ , A) ⊢ B) → ⊨ A → Hole → Frame Γ (Δ , A) B B
\end{code}

An element of type Frame Γ Δ A B is an "expression node" of type ⊢ A with a
hole of type Δ ⊢ B. It represents a computation in context Γ, (possibly waiting for a value of type B computed in context Δ) to produce a value of type A.
Note that most frames don't change context (Γ = Δ), but app₃ does.

What each type parameter of `Stack Answer Γ Δ T` means:
  - The base context (prior to any occurances of function application) is Γ.
  - The current hole context is Δ
  - The hole is in the place of a term of type T.

\begin{code}
data Stack (Answer : Type) : Context → Context → Type → Set where
  []  : Stack Answer Γ Γ Answer 
  _∷_ : Stack Answer Γ Δ A → Frame Δ Δ′ A B → Stack Answer Γ Δ′ B
\end{code}

A stack is a list of frames, sometimes called a zipper, a path into an
“expression tree”. An element of type Stack Answer A is an “expression
tree” of type ⊢ Answer with a hole of type ⊢ A.

The machine is in one of three modes:
●  _↑_: call mode (going up the tree), an expression is evaluated;
●  _↓_: return mode (going down the tree), a value is returned.

\begin{code}
data State : Context → Type → Set where
  -- Δ is the current context, δ is its environment
  _⊢_↓_ : (δ : Environment Δ) → Stack Answer Γ Δ T → ⊨ T → State Γ Answer
  _⊢_↑_ : (δ : Environment Δ) → Stack Answer Γ Δ T → Δ ⊢ T → State Γ Answer
\end{code}

step as a function.

\begin{code}
-- next : State Γ Answer → State Γ Answer
-- next (δ ⊢ [] ↓ v) = δ ⊢ [] ↓ v

-- next (δ ⊢ s ↑ ` x) = δ ⊢ s ↓ x
-- next (δ ⊢ s ↑ Var x) = δ ⊢ s ↓ lookupₑ δ x

-- next (δ ⊢ s ↑ 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) = δ ⊢ s ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↑ e
-- next (δ ⊢ s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true) = δ ⊢ s ↑ e₁
-- next (δ ⊢ s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false) = δ ⊢ s ↑ e₂

-- next (δ ⊢ s ↑ 𝚝𝚎𝚜𝚝 e) = δ ⊢ s ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e
-- next (δ ⊢ s ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ v) = δ ⊢ s ↓ test v

-- next (δ ⊢ s ↑ (e₁ ⊞ e₂)) = δ ⊢ s ∷ (◌ ⊞₀ e₂) ↑ e₁
-- next (δ ⊢ s ∷ (◌ ⊞₀ e₂) ↓ v) = δ ⊢ s ∷ (v ⊞₁ ◌) ↑ e₂
-- next (δ ⊢ s ∷ (n₀ ⊞₁ ◌) ↓ v) = δ ⊢ s ↓ (n₀ + v)

-- next (δ ⊢ s ↑ (ƛ e)) = δ ⊢ s ↓ ⟨ δ , e ⟩
-- next (δ ⊢ s ↑ (e₁ · e₂)) = δ ⊢ s ∷ app₁ ◌ e₂ ↑ e₁
-- next (δ ⊢ s ∷ app₁ ◌ e₂ ↓ v) = δ ⊢ s ∷ app₂ v ◌ ↑ e₂
-- next (δ ⊢ s ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌ ↓ v) = (δᶜ , v) ⊢ s ∷ app₃ δ δᶜ eᶜ v ◌ ↑ eᶜ
-- next (δ' ⊢ s ∷ app₃ δ δᶜ eᶜ v₂ ◌ ↓ v) = δ ⊢ s ↓ v
-- where δ' = (δᶜ , v₂).
\end{code}

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

step as a relation.
\begin{code}
private variable
  s : Stack Answer Γ Δ T

data _⇾_ : State Γ Answer → State Γ Answer → Set where
  step-` : ∀ {x : ⊨ A} → (δ ⊢ s ↑ ` x) ⇾ (δ ⊢ s ↓ x)
  step-Var : (δ ⊢ s ↑ Var x) ⇾ (δ ⊢ s ↓ lookupₑ δ x)
  step-𝚒𝚏  : (δ ⊢ s ↑ 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) ⇾ (δ ⊢ s ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↑ e)
  step-𝚝𝚑𝚎𝚗 : (δ ⊢ s ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↓ true) ⇾ (δ ⊢ s ↑ e₁)
  step-𝚎𝚕𝚜𝚎 : (δ ⊢ s ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↓ false) ⇾ (δ ⊢ s ↑ e₂)
  
  step-𝚝𝚎𝚜𝚝₁ : (δ ⊢ s ↑ 𝚝𝚎𝚜𝚝 e) ⇾ (δ ⊢ s ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e)
  step-𝚝𝚎𝚜𝚝₂ : (δ ⊢ s ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ v) ⇾ (δ ⊢ s ↓ test v)

  step-⊞₁ : (δ ⊢ s ↑ (e₁ ⊞ e₂)) ⇾ (δ ⊢ s ∷ (◌ ⊞₀ e₂) ↑ e₁)
  step-⊞₂ : (δ ⊢ s ∷ (◌ ⊞₀ e₂) ↓ v) ⇾ (δ ⊢ s ∷ (v ⊞₁ ◌) ↑ e₂)
  step-⊞₃ : (δ ⊢ s ∷ (n₀ ⊞₁ ◌) ↓ v) ⇾ (δ ⊢ s ↓ (n₀ + v))
  
  step-ƛ : (δ ⊢ s ↑ (ƛ e)) ⇾ (δ ⊢ s ↓ ⟨ δ , e ⟩)
  step-· : (δ ⊢ s ↑ (e₁ · e₂)) ⇾ (δ ⊢ s ∷ app₁ ◌ e₂ ↑ e₁)
  step-·₁ : (δ ⊢ s ∷ app₁ ◌ e₂ ↓ v) ⇾ (δ ⊢ s ∷ app₂ v ◌ ↑ e₂)
  step-·₂ : ∀ {v : ⊨ T} → (δ ⊢ s ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌ ↓ v) ⇾ ((δᶜ , v) ⊢ s ∷ app₃ δ δᶜ eᶜ v ◌ ↑ eᶜ)
  step-·₃ : ∀ {v₁ : ⊨ A} {v : ⊨ B} {h₌ : δ′ ≡ (δᶜ , v₁) }
          → (δ′ ⊢ s ∷ app₃ δ δᶜ eᶜ v₁ ◌ ↓ v) ⇾ (δ ⊢ s ↓ v)

data _⇾⃰_ : State Γ Answer → State Γ Answer → Set where
  base  : ∀ {s : State Γ Answer}        → s ⇾⃰ s
  step  : ∀ {s₀ s₁ s₂ : State Γ Answer} → s₀ ⇾ s₁ → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₂
\end{code}


Reconstruct an expression from a stack and an expression at the hole position.

\begin{code}
_[_] : Stack Answer Γ Δ T → Δ ⊢ T → Γ ⊢ Answer
[] [ e ] = e
(s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂)   [ e ] = s [ 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂ ]
(s ∷ ◌ ⊞₀ e₂)      [ e ] = s [ e ⊞ e₂ ]
(s ∷ n₀ ⊞₁ ◌)      [ e ] = s [ ` n₀ ⊞ e ]
(s ∷ 𝚝𝚎𝚜𝚝 ◌)       [ e ] = s [ 𝚝𝚎𝚜𝚝 e ]
(s ∷ app₁ ◌ e₂)      [ e ] = s [ e · e₂ ]
(s ∷ app₂ f ◌)       [ e ] = s [ ` f · e ]
-- (s ∷ app₃ δ δᶜ eᶜ x ◌) [ e ] = s [ {! e!} ]
(s ∷ app₃ δ δᶜ eᶜ x ◌) [ e ] = s [ ` ⟨ δᶜ , e ⟩ · ` x ]
-- app₃: We'revaluating closure body e : (Δ , A) ⊢ B
-- Stack takes e and produces expression in base context Γ
\end{code}
