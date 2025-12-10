A small-step machine for Mini.

correctness:   ([] ↑ e) ⇾⃰ ([] ↓ v)  →  e ⇓ v
completeness:  e ⇓ v  →  ([] ↑ e) ⇾⃰ ([] ↓ v)

%------------------------------------------------------------------------------

\begin{code}
-- {-# OPTIONS --safe --without-K #-}
-- {-# OPTIONS --without-K #-}

module STLC.Simplified where

open import STLC.Mini2
  hiding (deterministic; Frame; Stack; State; {- base; -} step)
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
-- private
--   variable
--     n n₀ n₁ : ℕ
--     A B Answer : Type
private variable
  Γ Δ : Context
  δ : Environment Γ
  A B T Answer : Type
  
  n n₀ n₁ : ℕ
  v v₁ v₂ : ⊨ A
  e₁ e₂ e₃ : Γ ⊢ A 

\end{code}

-------------------------------------------------------------------------------

A small-step machine.

\begin{code}
data Frame : Type → Type → Set where
  _𝚎𝚕𝚜𝚎_ : Γ ⊢ A → Γ ⊢ A → Frame A Type.𝙱𝚘𝚘𝚕
  _⊞₀_   : Hole → Γ ⊢ 𝙽𝚊𝚝 → Frame 𝙽𝚊𝚝 𝙽𝚊𝚝
  _⊞₁_   : δ ⊢ e₁ ⇓ n₁ → Hole → Frame 𝙽𝚊𝚝 𝙽𝚊𝚝
  𝚝𝚎𝚜𝚝   : Hole → Frame 𝙱𝚘𝚘𝚕 𝙽𝚊𝚝
  app₁    : Hole → Γ ⊢ A → Frame T (A ⇒ B)
  app₂    : δ ⊢ e₁ ⇓ v₁ → Hole → Frame T A
  app₃    : δ ⊢ e₁ ⇓ v₁ → δ ⊢ e₂ ⇓ v₂ → Hole → Frame T A
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
  -- _↑_ : Stack Answer A → ⊢ A → State Answer
  -- _↓_ : Stack Answer A → ⊨ A → State Answer
  _⊢_↓_ : {Γ : Context} → (δ : Environment Γ) → Stack Answer T → {e : Γ ⊢ T} → δ ⊢ e ⇓ v → State Answer
  _⊢_↑_ : (δ : Environment Γ) → Stack Answer T → Γ ⊢ T → State Answer
\end{code}

\begin{code}
private
  variable
    stack : Stack Answer A
\end{code}

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

step as a function.

\begin{code}
next : State Answer → State Answer
next s = ?
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
data _⇾_ : State Answer → State Answer → Set where
  step-𝚝𝚑𝚎𝚗  :  ∀ {e} {e₁ e₂ : Γ ⊢ A} {p : δ ⊢ e ⇓ true}  → (δ ⊢ stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↓ p) ⇾  (δ ⊢ stack ↑ e₁)
  step-𝚎𝚕𝚜𝚎  :  ∀ {e} {e₁ e₂ : Γ ⊢ A} {p : δ ⊢ e ⇓ false} → (δ ⊢ stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↓ p) ⇾  (δ ⊢ stack ↑ e₂)
  step-⊞₁    :  ∀ {e₀ e₁ : Γ ⊢ 𝙽𝚊𝚝} {p : δ ⊢ e₀ ⇓ n₀}     → (δ ⊢ stack ∷ (◌ ⊞₀ e₁)    ↓ p) ⇾  (δ ⊢ stack ∷ (p ⊞₁ ◌) ↑ e₁)
  step-⊞₂    :  ∀ {e₀ e₁ : Γ ⊢ 𝙽𝚊𝚝} {n₀ n₁ : ℕ} {p₁ : δ ⊢ e₀ ⇓ n₀} {p₂ : δ ⊢ e₁ ⇓ n₁} 
             → (δ ⊢ stack ∷ (p₁ ⊞₁ ◌) ↓ p₂) ⇾  (δ ⊢ stack ↓ ` (n₀ + n₁))
  
  step-𝚝𝚎𝚜𝚝₁ : ∀ {e₀ : Γ ⊢ 𝙽𝚊𝚝} {n₀ : ℕ} {p : δ ⊢ e₀ ⇓ n₀}
            →  (δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌       ↓ p) ⇾  (δ ⊢ stack ↓ 𝚝𝚎𝚜𝚝 p)
  
  step-`     :  ∀ {v : ⊨ A}                       → (δ ⊢ stack ↑ ` v)                    ⇾  (δ ⊢ stack ↓ ` v)
  step-𝚒𝚏    :  ∀ {e₀ : Γ ⊢ 𝙱𝚘𝚘𝚕} {e₁ e₂ : Γ ⊢ A} → (δ ⊢ stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂)  ⇾  (δ ⊢ stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↑ e₀)
  step-⊞₀    :  ∀ {e₀ e₁ : Γ ⊢ 𝙽𝚊𝚝}               → (δ ⊢ stack ↑ e₀ ⊞ e₁)                ⇾  (δ ⊢ stack ∷ (◌ ⊞₀ e₁) ↑ e₀)
  step-𝚝𝚎𝚜𝚝₀ :  ∀ {e : Γ ⊢ 𝙽𝚊𝚝}                   → (δ ⊢ stack ↑ 𝚝𝚎𝚜𝚝 e)                 ⇾  (δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e)
\end{code}

\begin{code}
data _⇾⃰_ : State Answer → State Answer → Set where
  base  : ∀ {s : State Answer}        → s ⇾⃰ s
  step  : ∀ {s₀ s₁ s₂ : State Answer} → s₀ ⇾ s₁ → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₂
\end{code}

\begin{code}
⇾⃰-reflexive : ∀ {s : State Answer} → s ⇾⃰ s
⇾⃰-reflexive = base

⇾⃰-transitive : ∀ {s₀ s₁ s₂ : State Answer} → s₀ ⇾⃰ s₁ → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₂
⇾⃰-transitive (base)      q = q
⇾⃰-transitive (step s p)  q = step s (⇾⃰-transitive p q)
\end{code}

The relation ⇾ is deterministic.

\begin{code}
deterministic : ∀ {s s′ s″ : State Answer} → s ⇾ s′ → s ⇾ s″ → s′ ≡ s″
deterministic step-𝚝𝚑𝚎𝚗 step-𝚝𝚑𝚎𝚗 = reflexive
deterministic step-𝚎𝚕𝚜𝚎 step-𝚎𝚕𝚜𝚎 = reflexive
deterministic step-⊞₁ step-⊞₁ = reflexive
deterministic step-⊞₂ step-⊞₂ = reflexive
deterministic step-𝚝𝚎𝚜𝚝₁ step-𝚝𝚎𝚜𝚝₁ = reflexive
deterministic step-` step-` = reflexive
deterministic step-𝚒𝚏 step-𝚒𝚏 = reflexive
deterministic step-⊞₀ step-⊞₀ = reflexive
deterministic step-𝚝𝚎𝚜𝚝₀ step-𝚝𝚎𝚜𝚝₀ = reflexive
-- deterministic step-throw step-throw = reflexive
-- deterministic step-drop₁ step-drop₁ = reflexive
-- deterministic step-drop₂ step-drop₂ = reflexive
-- deterministic step-drop₃ step-drop₃ = reflexive
-- deterministic step-drop₄ step-drop₄ = reflexive
-- deterministic step-try step-try = reflexive
-- deterministic step-exn step-exn = reflexive
-- deterministic step-ok step-ok = reflexive
\end{code}

The relation ⇾ is (almost) total: for each non-final state there is a
follow-up state.

<<total>>
\begin{code}
data Final {Answer : Type} : State Answer → Set where
  final₁ : ∀ {e} {v : ⊨ Answer} {p : ∅ ⊢ e ⇓ v}  → Final (∅ ⊢ [] ↓ p)

total : ∀ (s : State Answer) → ¬ Final s → ∃ (λ s′ → s ⇾ s′)
total s ¬final = ?
-- total (δ ⊢ stack ↑ ` x) ¬final = δ ⊢ stack ↓ (x , step-`)
-- total (δ ⊢ stack ↑ 𝚒𝚏 x₁ 𝚝𝚑𝚎𝚗 x₂ 𝚎𝚕𝚜𝚎 x₃) ¬final = δ ⊢ stack ∷ x₂ 𝚎𝚕𝚜𝚎 x₃ ↑ x₁ , step-𝚒𝚏
-- total (δ ⊢ stack ↑ x₁ ⊞ x₂) ¬final = δ ⊢ stack ∷ ◌ ⊞₀ x₂ ↑ x₁ , step-⊞₀
-- total (δ ⊢ stack ↑ 𝚝𝚎𝚜𝚝 x₁) ¬final = δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ x₁ , step-𝚝𝚎𝚜𝚝₀
-- total (δ ⊢ [] ↓ v) ¬final = ex-falso-quodlibet (¬final final₁)
-- total (δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false) ¬final = δ ⊢ stack ↑ e₂ , step-𝚎𝚕𝚜𝚎
-- total (δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true) ¬final = δ ⊢ stack ↑ e₁ , step-𝚝𝚑𝚎𝚗
-- total (δ ⊢ stack ∷ ◌ ⊞₀ e₁ ↓ v) ¬final = δ ⊢ stack ∷ v ⊞₁ ◌ ↑ e₁ , step-⊞₁
-- total (δ ⊢ stack ∷ n₀ ⊞₁ ◌ ↓ v) ¬final = δ ⊢ stack ↓ n₀ + v , step-⊞₂
-- total (δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ v) ¬final = δ ⊢ stack ↓ test v , step-𝚝𝚎𝚜𝚝₁
\end{code}

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

The standard reasoning format.

<<reasoning>>
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

complete
  : ∀ (stack : Stack Answer A) (e : Γ ⊢ A) 
  → ∀ (v : ⊨ A) (p : δ ⊢ e ⇓ v) 
  → (δ ⊢ stack ↑ e) ⇾⃰ (δ ⊢ stack ↓ p)
complete stack e _ v = ?

-- complete stack (` v) _ (` v) = step step-` base
-- complete stack (𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) v (𝚒𝚏-𝚝𝚑𝚎𝚗 p₀ p₁ e₂) =
--   proof
--     (stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂)
--   ⇾⟨ step-𝚒𝚏 ⟩
--     stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↑ e₀
--   ⇾⃰⟨ complete (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) e₀ true p₀ ⟩
--     stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true
--   ⇾⟨ step-𝚝𝚑𝚎𝚗  ⟩
--     stack ↑ e₁
--   ⇾⃰⟨ complete stack e₁ v p₁ ⟩
--     (stack ↓ v)
--   ∎
-- complete stack (𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) v (𝚒𝚏-𝚎𝚕𝚜𝚎 p₀ e₁ p₂) =
--   proof
--     (stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂)
--   ⇾⟨ step-𝚒𝚏 ⟩
--     stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↑ e₀
--   ⇾⃰⟨ complete (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) e₀ false p₀ ⟩
--     stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false
--   ⇾⟨ step-𝚎𝚕𝚜𝚎 ⟩
--     stack ↑ e₂
--   ⇾⃰⟨ complete stack e₂ v p₂ ⟩
--     (stack ↓ v)
--   ∎
-- complete stack (e₀ ⊞ e₁) v (p₀ ⊞ p₁) =
--   proof
--     (stack ↑ e₀ ⊞ e₁)
--   ⇾⟨ step-⊞₀ ⟩
--     (stack ∷ ◌ ⊞₀ e₁ ↑ e₀)
--   ⇾⃰⟨ complete (stack ∷ ◌ ⊞₀ e₁) e₀ _ p₀ ⟩
--     (stack ∷ ◌ ⊞₀ e₁ ↓ _)
--   ⇾⟨ step-⊞₁ ⟩
--     (stack ∷ _ ⊞₁ ◌ ↑ e₁)
--   ⇾⃰⟨ complete (stack ∷ _ ⊞₁ ◌) e₁ _ p₁ ⟩
--     (stack ∷ _ ⊞₁ ◌ ↓ _)
--   ⇾⟨ step-⊞₂ ⟩
--     (stack ↓ v)
--   ∎
-- complete stack (𝚝𝚎𝚜𝚝 e) v (𝚝𝚎𝚜𝚝 p) =
--   proof
--     (stack ↑ 𝚝𝚎𝚜𝚝 e)
--   ⇾⟨ step-𝚝𝚎𝚜𝚝₀ ⟩
--     (stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e)
--   ⇾⃰⟨ complete (stack ∷ 𝚝𝚎𝚜𝚝 ◌) e _ p ⟩
--     (stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ _)
--   ⇾⟨ step-𝚝𝚎𝚜𝚝₁ ⟩
--     stack ↓ v
--   ∎

-- complete stack t v = ?

complete´ 
  : ∀ (e : Γ ⊢ A) (v : ⊨ A)
  → (p : δ ⊢ e ⇓ v)
  → ∀ {s : Stack Answer A} 
  → (δ ⊢ s ↑ e) ⇾⃰ (δ ⊢ s ↓ p)
complete´ e v p = complete _ e v p
\end{code}

\begin{code}
Total :  ∀ (e : Γ ⊢ A) → ∃ (λ v → (δ ⊢ stack ↑ e) ⇾⃰ (δ ⊢ stack ↓ v))
Total = ? -- with ↓-total e
-- ... | v , p = v , complete _ e v p
\end{code}

-------------------------------------------------------------------------------

apply : Stack Answer A → ⊢ A → ⊢ Answer
apply [] e = e
apply (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) e = apply stack (𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂)
apply (stack ∷ ◌ ⊞₀ e₁)    e = apply stack (e ⊞ e₁)
apply (stack ∷ v₀ ⊞₁ ◌)    e = apply stack (` v₀ ⊞ e)
apply (stack ∷ 𝚝𝚎𝚜𝚝 ◌)     e = apply stack (𝚝𝚎𝚜𝚝 e)

\begin{code}
_[_] : Stack Answer A → Γ ⊢ A → Γ ⊢ Answer
[]               [ e ] = e
(s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) [ e ] = s [ 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂ ]
(s ∷ ◌ ⊞₀ e₁)    [ e ] = s [ e ⊞ e₁ ]
(s ∷ v₀ ⊞₁ ◌)    [ e ] = s [ ` v₀ ⊞ e ]
(s ∷ 𝚝𝚎𝚜𝚝 ◌)     [ e ] = s [ 𝚝𝚎𝚜𝚝 e ]
\end{code}

zip : State Answer → ⊢ Answer
zip (δ ⊢ stack ↓ v) = apply stack (` v)
zip (δ ⊢ stack ↑ e) = apply stack e

\begin{code}
expr : State Answer → Γ ⊢ Answer
expr (δ ⊢ s ↓ v) = s [ ` v ]
expr (δ ⊢ s ↑ e) = s [ e ]
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

-- private variable
  -- e₁ e₂ : ⊢ A
  -- C : Frame _ A

mutual
  ⪅-compositional : {e e′ : Γ ⊢ A} → e ⪅ e′ → ∀ (s : Stack Answer A) → s [ e ] ⪅ s [ e′ ]
  ⪅-compositional r [] = r
  ⪅-compositional r (s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) = ⪅-compositional (if-ctx r) s
  ⪅-compositional r (s ∷ ◌  ⊞₀ e₁)   = ⪅-compositional (plus-ctx₁ r) s
  ⪅-compositional r (s ∷ n₀ ⊞₁  ◌)   = ⪅-compositional (plus-ctx₂ r) s
  ⪅-compositional r (s ∷    𝚝𝚎𝚜𝚝 ◌)  = ⪅-compositional (test-ctx r) s

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
\end{code}

\begin{code}
step′ : ∀ {s s′ : State A} → s ⇾ s′ → expr s′ ⪅ expr s
step′ {s = δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true}  step-𝚝𝚑𝚎𝚗 p = ⪅-compositional if-then-refine stack p
step′ {s = δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false} step-𝚎𝚕𝚜𝚎 p = ⪅-compositional if-else-refine stack p
step′ {s = δ ⊢ stack ∷ ◌ ⊞₀ e₁ ↓ n₀} step-⊞₁ p = p
step′ {s = δ ⊢ stack ∷ n₀ ⊞₁ ◌ ↓ n₁} step-⊞₂ p = ⪅-compositional plus-refine stack p
step′ {s = δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ n} step-𝚝𝚎𝚜𝚝₁ p = ⪅-compositional test-refine stack p
step′ {s = δ ⊢ stack ↑ ` v} step-` p = p
step′ {s = δ ⊢ stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂} step-𝚒𝚏 p = p
step′ {s = δ ⊢ stack ↑ e₀ ⊞ e₁} step-⊞₀ p = p
step′ {s = δ ⊢ stack ↑ 𝚝𝚎𝚜𝚝 e} step-𝚝𝚎𝚜𝚝₀ p = p

identity : ∀ {A : Set} -> A -> A
identity a = a

step″ : ∀ s {s′ : State A} → s ⇾ s′ → expr s′ ⪅ expr s
step″ (δ ⊢ s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true)  step-𝚝𝚑𝚎𝚗 = ⪅-compositional if-then-refine s
step″ (δ ⊢ s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false) step-𝚎𝚕𝚜𝚎 = ⪅-compositional if-else-refine s
step″ (δ ⊢ s ∷ ◌ ⊞₀ e₁ ↓ n₀) step-⊞₁ = identity
step″ (δ ⊢ s ∷ n₀ ⊞₁ ◌ ↓ n₁) step-⊞₂ = ⪅-compositional plus-refine s
step″ (δ ⊢ s ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ n) step-𝚝𝚎𝚜𝚝₁ = ⪅-compositional test-refine s
step″ (δ ⊢ s ↑ ` v) step-` = identity
step″ (δ ⊢ s ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) step-𝚒𝚏 = identity
step″ (δ ⊢ s ↑ e₀ ⊞ e₁) step-⊞₀ = identity
step″ (δ ⊢ s ↑ 𝚝𝚎𝚜𝚝 e) step-𝚝𝚎𝚜𝚝₀ = identity
\end{code}

\begin{code}
simulateᴿ : ∀ {s s′ : State A} → s ⇾⃰ s′ → expr s′ ⪅ expr s
simulateᴿ (base)      q = q
-- simulateᴿ (step p ps) q = step″ _ p (simulateᴿ ps q)
simulateᴿ (step p ps) q = step′ p (simulateᴿ ps q)

correct : ∀ {e : Γ ⊢ A} {v : ⊨ A} → (∅ ⊢ [] ↑ e ⇾⃰  ∅ ⊢ [] ↓ v) → ∅ ⊢ e ⇓ v
correct p = simulateᴿ p (` _)
\end{code}

-------------------------------------------------------------------------------

