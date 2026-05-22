A small-step machine for Mini.

correctness:   ([] ↑ e) ⇾⃰ ([] ↓ v)  →  e ⇓ v
completeness:  e ⇓ v  →  ([] ↑ e) ⇾⃰ ([] ↓ v)

%------------------------------------------------------------------------------

\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module STLC-Alt.Simplified where

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
  Γ Δ : Context
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
data Frame : Context → Type → Type → Set where
  _𝚎𝚕𝚜𝚎_  : Γ ⊢ A     → Γ ⊢ A   → Frame Γ A Type.𝙱𝚘𝚘𝚕
  _⊞₀_    : Hole      → Γ ⊢ 𝙽𝚊𝚝 → Frame Γ 𝙽𝚊𝚝 𝙽𝚊𝚝
  _⊞₁_    : ⊨ 𝙽𝚊𝚝     → Hole    → Frame Γ 𝙽𝚊𝚝 𝙽𝚊𝚝
  𝚝𝚎𝚜𝚝    : Hole                → Frame Γ 𝙱𝚘𝚘𝚕 𝙽𝚊𝚝
  app₁    : Hole      → Γ ⊢ A   → Frame Γ B (A ⇒ B)
  app₂    : ⊨ (A ⇒ B) → Hole    → Frame Γ B A
  app₃    : (δ : Environment Δ) → ⊨ (A ⇒ B) → ⊨ A     → Hole → Frame Γ B B
\end{code}

An element of type Frame A B is an “expression node” of type ⊢ A with a
hole of type ⊢ B.

\begin{code}
data Stack (Γ : Context) (Answer : Type) : Type → Set where
  []  : Stack Γ Answer Answer 
  _∷_ : Stack Γ Answer A → Frame Γ A B → Stack Γ Answer B
\end{code}

A stack is a list of frames, sometimes called a zipper, a path into an
“expression tree”. An element of type Stack Answer A is an “expression
tree” of type ⊢ Answer with a hole of type ⊢ A.

The machine is in one of three modes:
●  _↑_: call mode (going up the tree), an expression is evaluated;
●  _↓_: return mode (going down the tree), a value is returned.

\begin{code}
data State (Γ : Context) (Answer : Type) : Set where
  _⊢_↓_ : (δ : Environment Γ) → Stack Γ Answer T →   ⊨ T → State Γ Answer
  _⊢_↑_ : (δ : Environment Γ) → Stack Γ Answer T → Γ ⊢ T → State Γ Answer
\end{code}

\begin{code}
private
  variable
    stack : Stack Γ Answer A
\end{code}

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

step as a function.
NOTE: We cannot describe the step relation functionally. Both `Frame` and the Stack constructors bring in arbitrary contexts.
When modeling these as constructors in a datatype, this is dealt with via unification. 
If we fill a hole expecting a `Γ₁ ⊢ A` with an expression of type `Γ ⊢ A`, then the type checker adds a constraint `Γ ~ Γ₁`.

\begin{code}
-- next : State Answer → State Answer
-- next s = ?
-- next ([] ↓ v) = [] ↓ v

-- next (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↓ v) = stack ↑ (if v then e₁ else e₂)
-- next (stack ∷ (◌ ⊞₀ e₁)    ↓ v) = stack ∷ (v ⊞₁ ◌) ↑ e₁
-- next (stack ∷ (n₀ ⊞₁ ◌)    ↓ v) = stack ↓ n₀ + v
-- next (stack ∷ 𝚝𝚎𝚜𝚝 ◌       ↓ v) = stack ↓ test v
-- next (stack ∷ ◌ catch x₂   ↓ v) = stack ↓ v

-- next (stack ↑ ` v)                   = stack ↓ v
-- next (stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) = stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↑ e₀
-- next (stack ↑ e₀ ⊞ e₁)               = stack ∷ (◌ ⊞₀ e₁) ↑ e₀
-- next (stack ↑ 𝚝𝚎𝚜𝚝 e)                = stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e
-- next (stack ↑ throw) = stack ↯
-- next (stack ↑ try x₁ catch x₂) = stack ∷ (◌ catch x₂) ↑ x₁

-- next ([] ↯) = [] ↯
-- next (stack ∷ (x 𝚎𝚕𝚜𝚎 x₁) ↯) = stack ↯
-- next (stack ∷ (x ⊞₀ x₁) ↯) = stack ↯
-- next (stack ∷ (x ⊞₁ x₁) ↯) = stack ↯
-- next (stack ∷ 𝚝𝚎𝚜𝚝 x ↯) = stack ↯
-- next (stack ∷ (◌ catch h) ↯) = stack ↑ h
\end{code}

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

step as a relation.

\begin{code}
data _⇾_ : {Γ Γ′ : Context} → State Γ Answer → State Γ′ Answer → Set where
  step-`  : ∀ {stack : Stack Γ Answer A} {v : ⊨ A} → (δ ⊢ stack ↑ ` v) ⇾ (δ ⊢ stack ↓ v) 
  step-⊞₁ : (δ ⊢ stack ↑ e₁ ⊞ e₂) ⇾ (δ ⊢ stack ∷ ◌ ⊞₀ e₂ ↑ e₁) 
  step-⊞₂ : (δ ⊢ stack ∷ ◌ ⊞₀ e₂ ↓ v₁) ⇾ (δ ⊢ stack ∷ v₁ ⊞₁ ◌ ↑ e₂) 
  step-⊞₃ : (δ ⊢ stack ∷ v₁ ⊞₁ ◌ ↓ v₂) ⇾ (δ ⊢ stack ↓ (v₁ + v₂)) 
  step-𝚝𝚎𝚜𝚝₁ : (δ ⊢ stack ↑ 𝚝𝚎𝚜𝚝 e) ⇾ (δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e) 
  step-𝚒𝚏 : (δ ⊢ stack ↑ 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) ⇾ (δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↑ e) 
  step-𝚝𝚑𝚎𝚗 : (δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true) ⇾ (δ ⊢ stack ↑ e₁)
  step-𝚎𝚕𝚜𝚎 : (δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false) ⇾ (δ ⊢ stack ↑ e₂) 
  step-var : (δ ⊢ stack ↑ Var x) ⇾ (δ ⊢ stack ↓ lookupₑ δ x) 
  step-· : (δ ⊢ stack ↑ (e₁ · e₂)) ⇾ (δ ⊢ stack ∷ app₁ ◌ e₂ ↑ e₁) 
  step-ƛ : (δ ⊢ stack ↑ (ƛ e)) ⇾ (δ ⊢ stack ↓ ⟨ δ , e ⟩) 
  step-𝚝𝚎𝚜𝚝₂ : (δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ v) ⇾ (δ ⊢ stack ↓ test v) 
  step-·₁ : (δ ⊢ stack ∷ app₁ ◌ e₂ ↓ v₁) ⇾ (δ ⊢ stack ∷ app₂ v₁ ◌ ↑ e₂)
  step-·₂ : ∀ {v₂ : ⊨ A}
          → (δ ⊢ stack ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌ ↓ v₂) ⇾ ((δᶜ , v₂) ⊢ stack ∷ app₃ δ ⟨ δᶜ , eᶜ ⟩ v₂ ◌ ↑ eᶜ) 
  step-·₃ : ∀ {stack} {v₁ : ⊨ (A ⇒ B)} {v₂ : ⊨ A}
          → (δ ⊢ stack ∷ app₃ δ′ ⟨ δᶜ , eᶜ ⟩ v₂ ◌ ↓ v₃) ⇾ (δ′ ⊢ stack ↓ v₃) 
\end{code}

\begin{code}
data _⇾⃰_ : {Γ₁ Γ₂ : Context} → State Γ₁ Answer → State Γ₂ Answer → Set where
  base  : ∀ {s : State Γ Answer}        → s ⇾⃰ s
  step  : ∀ {Γ₁ Γ₂ Γ₃}
            {s₀ : State Γ₁ Answer} 
            {s₁ : State Γ₂ Answer} 
            {s₂ : State Γ₃ Answer} 
          → s₀ ⇾ s₁ → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₂
\end{code}

\begin{code}
postulate
  ⇾⃰-reflexive : ∀ {s : State Γ Answer} → s ⇾⃰ s
-- ⇾⃰-reflexive = base

postulate
  ⇾⃰-transitive : ∀ {s₀ s₁ s₂ : State Γ Answer} → s₀ ⇾⃰ s₁ → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₂
-- ⇾⃰-transitive (base)      q = q
-- ⇾⃰-transitive (step s p)  q = step s {! ⇾⃰-transitive  !} -- step s (⇾⃰-transitive p q)
\end{code}

The relation ⇾ is deterministic.

\begin{code}
deterministic : ∀ {s s′ s″ : State Γ Answer} → s ⇾ s′ → s ⇾ s″ → s′ ≡ s″
deterministic step-` step-` = reflexive
deterministic step-⊞₁ step-⊞₁ = reflexive
deterministic step-⊞₂ step-⊞₂ = reflexive
deterministic step-⊞₃ step-⊞₃ = reflexive
deterministic step-𝚝𝚎𝚜𝚝₁ step-𝚝𝚎𝚜𝚝₁ = reflexive
deterministic step-𝚒𝚏 step-𝚒𝚏 = reflexive
deterministic step-𝚝𝚑𝚎𝚗 step-𝚝𝚑𝚎𝚗 = reflexive
deterministic step-𝚎𝚕𝚜𝚎 step-𝚎𝚕𝚜𝚎 = reflexive
deterministic step-var step-var = reflexive
deterministic step-· step-· = reflexive
deterministic step-ƛ step-ƛ = reflexive
deterministic step-𝚝𝚎𝚜𝚝₂ step-𝚝𝚎𝚜𝚝₂ = reflexive
deterministic step-·₁ step-·₁ = reflexive
deterministic step-·₂ step-·₂ = reflexive
deterministic step-·₃ step-·₃ = reflexive
\end{code}

The relation ⇾ is (almost) total: for each non-final state there is a
follow-up state.

<<total>>
\begin{code}
-- data Final {Answer : Type} : State Γ Answer → Set where
--   final₁ : ∀ {v : ⊨ Answer} → Final (δ ⊢ [] ↓ v)

-- -- postulate
-- total : ∀ (s : State Γ Answer) → ¬ Final s → ∃ (λ s′ → s ⇾ s′)
-- total (δ ⊢ stack ↑ ` x) ¬final = δ ⊢ stack ↓ x ﹐ step-`
-- total (δ ⊢ stack ↑ e₁ ⊞ e₂) ¬final = δ ⊢ stack ∷ ◌ ⊞₀ e₂ ↑ e₁ ﹐ step-⊞₁
-- total (δ ⊢ stack ↑ 𝚝𝚎𝚜𝚝 e) ¬final = δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e ﹐ step-𝚝𝚎𝚜𝚝₁
-- total (δ ⊢ stack ↑ 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) ¬final = δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↑ e ﹐ step-𝚒𝚏
-- total (δ ⊢ stack ↑ Var x) ¬final = δ ⊢ stack ↓ lookupₑ δ x ﹐ step-var
-- total (δ ⊢ stack ↑ (e₁ · e₂)) ¬final = δ ⊢ stack ∷ app₁ ◌ e₂ ↑ e₁ ﹐ step-·
-- total (δ ⊢ stack ↑ (ƛ e)) ¬final = δ ⊢ stack ↓ ⟨ δ , e ⟩ ﹐ step-ƛ
-- total (δ ⊢ [] ↓ v) ¬final = ex-falso-quodlibet (¬final final₁)
-- total (δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false) ¬final = δ ⊢ stack ↑ e₂ ﹐ step-𝚎𝚕𝚜𝚎
-- total (δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true) ¬final = δ ⊢ stack ↑ e₁ ﹐ step-𝚝𝚑𝚎𝚗
-- total (δ ⊢ stack ∷ ◌  ⊞₀ e₂ ↓ v) ¬final = δ ⊢ stack ∷ v ⊞₁ ◌ ↑ e₂ ﹐ step-⊞₂
-- total (δ ⊢ stack ∷ e₁ ⊞₁ ◌ ↓ v) ¬final = δ ⊢ stack ↓ e₁ + v ﹐ step-⊞₃
-- total (δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ v) ¬final = δ ⊢ stack ↓ test v ﹐ step-𝚝𝚎𝚜𝚝₂
-- total (δ ⊢ stack ∷ app₁ ◌ e₂ ↓ v) ¬final = δ ⊢ stack ∷ app₂ v ◌ ↑ e₂ ﹐ step-·₁
-- total (δ ⊢ stack ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌ ↓ v) ¬final =  {!   !} ⊢ {!   !} ↑ {!   !} ﹐ {! step-·₂  !}
-- total (δ ⊢ stack ∷ app₃ δ₁ e₁ e₂ ◌ ↓ v) ¬final = (δ ⊢ stack ↓ v) ﹐ {!   !}
\end{code}

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

The standard reasoning format.

<<reasoning>>
\begin{code}
infix  0 proof_
infixr 1 ⇾-link ⇾⃰-link
infix  2 _∎

proof_ : {s₁ s₂ : State Γ Answer} → s₁ ⇾⃰ s₂ → s₁ ⇾⃰ s₂
proof s₁⇾⃰s₂ = s₁⇾⃰s₂

syntax ⇾-link x q p = x ⇾⟨ p ⟩ q
⇾-link : (s₀ : State Γ Answer) {s₁ s₂ : State Γ Answer} → s₁ ⇾⃰ s₂ → s₀ ⇾ s₁ → s₀ ⇾⃰ s₂
⇾-link _ q p = step p q

syntax ⇾⃰-link x q p = x ⇾⃰⟨ p ⟩ q
⇾⃰-link : (s₀ : State Γ Answer) {s₁ s₂ : State Γ Answer} → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₁ → s₀ ⇾⃰ s₂
⇾⃰-link _ q p = ⇾⃰-transitive p q

_∎ : (s : State Γ Answer) → s ⇾⃰ s
e ∎ = ⇾⃰-reflexive
\end{code}

  proof
    e
  ⇾⃰⟨ ? ⟩
    e
  ⇾⟨ ? ⟩
    e
  ∎

-------------------------------------------------------------------------------

Completeness.

\begin{code}

-- complete
--   : ∀ (δ : Environment Γ) (stack : Stack Γ Answer A) (e : Γ ⊢ A) 
--   → ∀ (v : ⊨ A) (p : δ ⊢ e ⇓ v) 
--   → (δ ⊢ stack ↑ e) ⇾⃰ (δ ⊢ stack ↓ v)
-- complete δ stack (` x) v (` .x) = step step-` base
-- complete δ stack (e₁ ⊞ e₂) v (_⊞_ {v₁ = v₁} {v₂ = v₂} p₁ p₂) =
--   proof
--     δ ⊢ stack ↑ e₁ ⊞ e₂
--   ⇾⟨ step-⊞₁ ⟩
--     δ ⊢ stack ∷ ◌ ⊞₀ e₂ ↑ e₁
--   ⇾⃰⟨ complete δ (stack ∷ ◌ ⊞₀ e₂) e₁ v₁ p₁ ⟩
--     δ ⊢ stack ∷ ◌ ⊞₀ e₂ ↓ v₁
--   ⇾⟨ step-⊞₂ ⟩
--     δ ⊢ stack ∷ v₁ ⊞₁ ◌ ↑ e₂
--   ⇾⃰⟨ complete δ (stack ∷ v₁ ⊞₁ ◌) e₂ v₂ p₂ ⟩
--     δ ⊢ stack ∷ v₁ ⊞₁ ◌ ↓ v₂
--   ⇾⟨ step-⊞₃ ⟩
--     δ ⊢ stack ↓ v₁ + v₂
--   ∎

-- complete δ stack (𝚝𝚎𝚜𝚝 e) v (𝚝𝚎𝚜𝚝 {n = n} p) =
--   proof
--     δ ⊢ stack ↑ 𝚝𝚎𝚜𝚝 e
--   ⇾⟨ step-𝚝𝚎𝚜𝚝₁ ⟩
--     δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e
--   ⇾⃰⟨ complete δ (stack ∷ 𝚝𝚎𝚜𝚝 ◌) e n p ⟩
--     δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ n
--   ⇾⟨ step-𝚝𝚎𝚜𝚝₂ ⟩
--     δ ⊢ stack ↓ test n
--   ∎

-- complete δ stack (𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) v (𝚒𝚏-𝚝𝚑𝚎𝚗 p p₁ e₃) =
--   proof
--     δ ⊢ stack ↑ 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂
--   ⇾⟨ step-𝚒𝚏 ⟩
--     δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↑ e
--   ⇾⃰⟨ complete δ (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) e true p ⟩
--     δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true
--   ⇾⟨ step-𝚝𝚑𝚎𝚗 ⟩
--     δ ⊢ stack ↑ e₁
--   ⇾⃰⟨ complete δ stack e₁ v p₁ ⟩
--     δ ⊢ stack ↓ v
--   ∎

-- complete δ stack (𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) v (𝚒𝚏-𝚎𝚕𝚜𝚎 p e₃ p₁) =
--   proof
--     δ ⊢ stack ↑ 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂
--   ⇾⟨ step-𝚒𝚏 ⟩
--     δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↑ e
--   ⇾⃰⟨ complete δ (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) e false p ⟩
--     δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false
--   ⇾⟨ step-𝚎𝚕𝚜𝚎 ⟩
--     δ ⊢ stack ↑ e₂
--   ⇾⃰⟨ complete δ stack e₂ v p₁ ⟩
--     δ ⊢ stack ↓ v
--   ∎

-- complete δ stack (Var x) v (var _) = step step-var base
-- complete δ stack (e₁ · e₂) v (app {δᶜ = δᶜ} {eᶜ} {v₂} p p₁ p₂) =
--   proof
--     δ ⊢ stack ↑ (e₁ · e₂)
--   ⇾⟨ step-· ⟩
--     δ ⊢ stack ∷ app₁ ◌ e₂ ↑ e₁
--   ⇾⃰⟨ complete δ (stack ∷ app₁ ◌ e₂) e₁ ⟨ δᶜ , eᶜ ⟩ p ⟩
--     δ ⊢ stack ∷ app₁ ◌ e₂ ↓ ⟨ δᶜ , eᶜ ⟩
--   ⇾⟨ step-·₁ ⟩
--     δ ⊢ stack ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌ ↑ e₂
--   ⇾⃰⟨ complete δ (stack ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌) e₂ v₂ p₁ ⟩
--     δ ⊢ stack ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌ ↓ v₂
--   ⇾⟨ {! step-·₂  !} ⟩ -- todo: types need to be fixed here. maybe app3 should modify the index of the Frame type?
--     {!   !}
--   ⇾⃰⟨ {!   !} ⟩
--     {!   !}
--   ⇾⟨ {!   !} ⟩
--     δ ⊢ stack ↓ v
--   ∎

-- complete δ stack (ƛ e) v (fun e₁) = step step-ƛ base

-- complete´ 
--   : ∀ (e : Γ ⊢ A) (v : ⊨ A)
--   → (p : δ ⊢ e ⇓ v)
--   → ∀ {s : Stack Γ Answer A} 
--   → (δ ⊢ s ↑ e) ⇾⃰ (δ ⊢ s ↓ v)
-- complete´ e v p = complete _ _ e v p
\end{code}

\begin{code}
-- Total :  ∀ (e : Γ ⊢ A) → ∃ (λ v → (δ ⊢ stack ↑ e) ⇾⃰ (δ ⊢ stack ↓ v))
-- Total e with ↓-total e
-- ... | x ﹐ p = x ﹐ complete _ _ e x p
\end{code}

-------------------------------------------------------------------------------

apply : Stack Answer A → ⊢ A → ⊢ Answer
apply [] e = e
apply (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) e = apply stack (𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂)
apply (stack ∷ ◌ ⊞₀ e₁)    e = apply stack (e ⊞ e₁)
apply (stack ∷ v₀ ⊞₁ ◌)    e = apply stack (` v₀ ⊞ e)
apply (stack ∷ 𝚝𝚎𝚜𝚝 ◌)     e = apply stack (𝚝𝚎𝚜𝚝 e)
  
\begin{code}
ƛ↑ : Closure A B → Γ ⊢ (A ⇒ B)
ƛ↑ c = ` c

_⊢_[_] : ∀ {Γ : Context} → Environment Γ → Stack Γ Answer A → Γ ⊢ A → Γ ⊢ Answer
δ ⊢ [] [ e ] = e
δ ⊢ (s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) [ e ] = δ ⊢ s [ 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂ ]
δ ⊢ (s ∷ ◌ ⊞₀ e₂) [ e ] = δ ⊢ s [ e ⊞ e₂ ]
δ ⊢ (s ∷ v₁ ⊞₁ ◌) [ e ] = δ ⊢ s [ ` v₁ ⊞ e ]
δ ⊢ (s ∷ 𝚝𝚎𝚜𝚝 ◌) [ e ] = δ ⊢ s [ 𝚝𝚎𝚜𝚝 e ]
δ ⊢ (s ∷ app₁ ◌ e₂) [ e ] = δ ⊢ s [ e · e₂ ]
δ ⊢ (s ∷ app₂ v₁ ◌) [ e ] = δ ⊢ s [ ` v₁ · e ]
δ ⊢ (s ∷ app₃ δ₁ v₁ v₂ ◌) [ e ] = δ ⊢ s [ e ]
\end{code}

zip : State Answer → ⊢ Answer
zip (δ ⊢ stack ↓ v) = apply stack (` v)
zip (δ ⊢ stack ↑ e) = apply stack e

\begin{code}
expr : State Γ Answer → Γ ⊢ Answer
expr (δ ⊢ s ↓ v) = δ ⊢ s [ ` v ]
expr (δ ⊢ s ↑ e) = δ ⊢ s [ e ]
\end{code}

-------------------------------------------------------------------------------

Correctness.  The proof below mimics the proof that small-step implies big-step.

\begin{code}
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

infix 2 _⪅_
_⪅_ : Γ ⊢ A → Γ ⊢ A → Set
e ⪅ e′  =  ∀ {δ} {v} → δ ⊢ e ⇓ v → δ ⊢ e′ ⇓ v  -- simulation / refinement

test-ctx : {e e′ : Γ ⊢ 𝙽𝚊𝚝} → e ⪅ e′ → 𝚝𝚎𝚜𝚝 e ⪅ 𝚝𝚎𝚜𝚝 e′
test-ctx r (𝚝𝚎𝚜𝚝 p) = 𝚝𝚎𝚜𝚝 (r p)

plus-ctx₁ : {e e′ e₁ : Γ ⊢ 𝙽𝚊𝚝} → e ⪅ e′ → e ⊞ e₁ ⪅ e′ ⊞ e₁
plus-ctx₁ r (p₁ ⊞ p₂) = r p₁ ⊞ p₂

plus-ctx₂ : {e e′ : Γ ⊢ 𝙽𝚊𝚝} → e ⪅ e′ → ` n₀ ⊞ e ⪅ ` n₀ ⊞ e′
plus-ctx₂ r (p₁ ⊞ p₂) = p₁ ⊞ r p₂

if-ctx : {e e′ : Γ ⊢ 𝙱𝚘𝚘𝚕} {e₁ e₂ : Γ ⊢ A}  → e ⪅ e′ → 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂ ⪅ 𝚒𝚏 e′ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂
if-ctx r (𝚒𝚏-𝚝𝚑𝚎𝚗 p₀ p₁ e₂) = 𝚒𝚏-𝚝𝚑𝚎𝚗 (r p₀) p₁ e₂
if-ctx r (𝚒𝚏-𝚎𝚕𝚜𝚎 p₀ e₁ p₂) = 𝚒𝚏-𝚎𝚕𝚜𝚎 (r p₀) e₁ p₂

app-ctx₁ : {f f′ : Γ ⊢ (A ⇒ B)} {x : Γ ⊢ A} → f ⪅ f′ → f · x ⪅ f′ · x
app-ctx₁ r (app c c₁ c₂) = app (r c) c₁ c₂

app-ctx₂ : {f : Γ ⊢ (A ⇒ B)} {x x′ : Γ ⊢ A} → x ⪅ x′ → f · x ⪅ f · x′
app-ctx₂ r (app c c₁ c₂) = app c (r c₁) c₂

-- How do we refine the body of the closure?
app-ctx₃ = {!   !}

-- private variable
  -- e₁ e₂ : ⊢ A
  -- C : Frame _ A

⪅-compositional : {e e′ : Γ ⊢ A} → e ⪅ e′ → ∀ (s : Stack Γ Answer A) → δ ⊢ s [ e ] ⪅ δ ⊢ s [ e′ ]
⪅-compositional r [] = r
⪅-compositional r (s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) = ⪅-compositional (if-ctx r) s
⪅-compositional r (s ∷ ◌  ⊞₀ e₁)   = ⪅-compositional (plus-ctx₁ r) s
⪅-compositional r (s ∷ n₀ ⊞₁  ◌)   = ⪅-compositional (plus-ctx₂ r) s
⪅-compositional r (s ∷    𝚝𝚎𝚜𝚝 ◌)  = ⪅-compositional (test-ctx r) s
⪅-compositional r (s ∷ app₁ x x₁) = ⪅-compositional (app-ctx₁ λ {δ = δ₃} {v = v₂} z → z) _
⪅-compositional r (s ∷ app₂ x x₁) = ⪅-compositional (app-ctx₂ λ {δ = δ₃} {v = v₂} z → z) _
⪅-compositional r (s ∷ app₃ δ x x₁ x₂) = ⪅-compositional (λ x₃ → x₃) {!   !}
\end{code}

...............................................................................

\begin{code}
plus-refine : ` (n₀ + n₁) ⪅ ` n₀ ⊞ ` n₁
plus-refine (` _) = ` _ ⊞ ` _

test-refine : ` test n ⪅ 𝚝𝚎𝚜𝚝 (` n)
test-refine (` _) = 𝚝𝚎𝚜𝚝 (` _)

if-then-refine : {e₁ e₂ : Γ ⊢ A} → e₁ ⪅ 𝚒𝚏 ` true 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂
if-then-refine p = 𝚒𝚏-𝚝𝚑𝚎𝚗 (` true)  p _

if-else-refine : {e₁ e₂ : Γ ⊢ A} → e₂ ⪅ 𝚒𝚏 ` false 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂
if-else-refine p = 𝚒𝚏-𝚎𝚕𝚜𝚎 (` false) _ p

-- fun-refine : {e₁ e₂ : Γ ⊢ A} → e₂ ⪅ (ƛ e₁) ∙ 
\end{code}

\begin{code}
step′ : ∀ {s s′ : State Γ A} → s ⇾ s′ → expr s′ ⪅ expr s
step′ = {!   !} 
-- step′ : ∀ {s s′ : State A} → s ⇾ s′ → expr s′ ⪅ expr s
-- step′ {s = δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true}  step-𝚝𝚑𝚎𝚗 p = ⪅-compositional if-then-refine stack p
-- step′ {s = δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false} step-𝚎𝚕𝚜𝚎 p = ⪅-compositional if-else-refine stack p
-- step′ {s = δ ⊢ stack ∷ ◌ ⊞₀ e₁ ↓ n₀} step-⊞₁ p = p
-- step′ {s = δ ⊢ stack ∷ n₀ ⊞₁ ◌ ↓ n₁} step-⊞₂ p = ⪅-compositional plus-refine stack p
-- step′ {s = δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ n} step-𝚝𝚎𝚜𝚝₁ p = ⪅-compositional test-refine stack p
-- step′ {s = δ ⊢ stack ↑ ` v} step-` p = p
-- step′ {s = δ ⊢ stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂} step-𝚒𝚏 p = p
-- step′ {s = δ ⊢ stack ↑ e₀ ⊞ e₁} step-⊞₀ p = p
-- step′ {s = δ ⊢ stack ↑ 𝚝𝚎𝚜𝚝 e} step-𝚝𝚎𝚜𝚝₀ p = p

identity : ∀ {A : Set} -> A -> A
identity a = a

step″ : ∀ s {s′ : State Γ A} → s ⇾ s′ → expr s′ ⪅ expr s
step″ (δ ⊢ s ↓ v) p = {!!}
step″ (δ ⊢ s ↑ e) p = {!!}
-- step″ (δ ⊢ s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true)  step-𝚝𝚑𝚎𝚗 = ⪅-compositional if-then-refine s
-- step″ (δ ⊢ s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false) step-𝚎𝚕𝚜𝚎 = ⪅-compositional if-else-refine s
-- step″ (δ ⊢ s ∷ ◌ ⊞₀ e₁ ↓ n₀) step-⊞₁ = identity
-- step″ (δ ⊢ s ∷ n₀ ⊞₁ ◌ ↓ n₁) step-⊞₂ = ⪅-compositional plus-refine s
-- step″ (δ ⊢ s ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ n) step-𝚝𝚎𝚜𝚝₁ = ⪅-compositional test-refine s
-- step″ (δ ⊢ s ↑ ` v) step-` = identity
-- step″ (δ ⊢ s ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) step-𝚒𝚏 = identity
-- step″ (δ ⊢ s ↑ e₀ ⊞ e₁) step-⊞₀ = identity
-- step″ (δ ⊢ s ↑ 𝚝𝚎𝚜𝚝 e) step-𝚝𝚎𝚜𝚝₀ = identity
\end{code}

\begin{code}
-- simulateᴿ : ∀ {s s′ : State Γ A} → s ⇾⃰ s′ → expr s′ ⪅ expr s
-- simulateᴿ (base)      q = q
-- -- simulateᴿ (step p ps) q = step″ _ p (simulateᴿ ps q)
-- simulateᴿ (step p ps) q = step′ p (simulateᴿ ps q)

-- correct : ∀ {e : Γ ⊢ A} {v : ⊨ A} → (∅ ⊢ [] ↑ e ⇾⃰  ∅ ⊢ [] ↓ v) → ∅ ⊢ e ⇓ v
-- correct p = simulateᴿ p (` _)
\end{code}

-------------------------------------------------------------------------------

