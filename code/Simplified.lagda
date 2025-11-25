A small-step machine for Mini.

correctness:   ([] ↑ e) ⇾⃰ ([] ↓ v)  →  e ⇓ v
completeness:  e ⇓ v  →  ([] ↑ e) ⇾⃰ ([] ↓ v)

%------------------------------------------------------------------------------

\begin{code}
-- {-# OPTIONS --safe --without-K #-}
{-# OPTIONS --without-K #-}

module Simplified where

open import Mini2
  hiding (deterministic; Frame; Stack; State; base; step)
  renaming (total to ↓-total)
  public

open import Data.Bool
open import Data.Nat renaming (_+_ to infixl 46 _+_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_) renaming (refl to reflexive)
open import Relation.Nullary.Negation
open import Data.Product using (∃; _,_)
open import Data.Empty using (⊥)

ex-falso-quodlibet : {A : Set} → ⊥ → A
ex-falso-quodlibet ()
\end{code}

\begin{code}
infixl 146 _⊞₀_ _⊞₁_
infix  120 _𝚎𝚕𝚜𝚎_c
infixr  35 _∷_
infix   30 _↓_ _↑_
\end{code}

\begin{code}
private
  variable
    n n₀ n₁ : ℕ
    A B Answer : Type
\end{code}

-------------------------------------------------------------------------------

A small-step machine.

\begin{code}
data Frame : Type → Type → Set where
  _𝚎𝚕𝚜𝚎_ : ⊢ A → ⊢ A → Frame A Type.𝙱𝚘𝚘𝚕
  _⊞₀_   : Hole → ⊢ 𝙽𝚊𝚝 → Frame 𝙽𝚊𝚝 𝙽𝚊𝚝
  _⊞₁_   : ⊨ 𝙽𝚊𝚝 → Hole → Frame 𝙽𝚊𝚝 𝙽𝚊𝚝
  𝚝𝚎𝚜𝚝   : Hole → Frame 𝙱𝚘𝚘𝚕 𝙽𝚊𝚝
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

The machine is in one of two modes:
●  _↑_: call mode (going up the tree), an expression is evaluated;
●  _↓_: return mode (going down the tree), a value is returned.

\begin{code}
data State (Answer : Type) : Set where
  _↑_ : Stack Answer A → ⊢ A → State Answer
  _↓_ : Stack Answer A → ⊨ A → State Answer
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
next ([] ↓ v) = [] ↓ v

next (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↓ v) = stack ↑ (if v then e₁ else e₂)
next (stack ∷ (◌ ⊞₀ e₁)    ↓ v) = stack ∷ (v ⊞₁ ◌) ↑ e₁
next (stack ∷ (n₀ ⊞₁ ◌)    ↓ v) = stack ↓ n₀ + v
next (stack ∷ 𝚝𝚎𝚜𝚝 ◌       ↓ v) = stack ↓ test v

next (stack ↑ ` v)                   = stack ↓ v
next (stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) = stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↑ e₀
next (stack ↑ e₀ ⊞ e₁)               = stack ∷ (◌ ⊞₀ e₁) ↑ e₀
next (stack ↑ 𝚝𝚎𝚜𝚝 e)                = stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e
\end{code}

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

step as a relation.

\begin{code}
data _⇾_ : State Answer → State Answer → Set where
  step-𝚝𝚑𝚎𝚗  :  ∀ {e₁ e₂ : ⊢ A}               → (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↓ true )   ⇾  (stack ↑ e₁)
  step-𝚎𝚕𝚜𝚎  :  ∀ {e₁ e₂ : ⊢ A}               → (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↓ false)   ⇾  (stack ↑ e₂)
  step-⊞₁    :  ∀ {e₁ : ⊢ 𝙽𝚊𝚝}                → (stack ∷ (◌ ⊞₀ e₁)    ↓ n₀)      ⇾  (stack ∷ (n₀ ⊞₁ ◌) ↑ e₁)
  step-⊞₂    :                                  (stack ∷ (n₀ ⊞₁ ◌)    ↓ n₁)      ⇾  (stack ↓ n₀ + n₁)
  step-𝚝𝚎𝚜𝚝₁ :                                  (stack ∷ 𝚝𝚎𝚜𝚝 ◌       ↓ n)       ⇾  (stack ↓ test n)
  
  step-`     :  ∀ {v : ⊨ A}                   → (stack ↑ ` v)                    ⇾  (stack ↓ v)
  step-𝚒𝚏    :  ∀ {e₀ : ⊢ 𝙱𝚘𝚘𝚕} {e₁ e₂ : ⊢ A} → (stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂)  ⇾  (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↑ e₀)
  step-⊞₀    :  ∀ {e₀ e₁ : ⊢ 𝙽𝚊𝚝}             → (stack ↑ e₀ ⊞ e₁)                ⇾  (stack ∷ (◌ ⊞₀ e₁) ↑ e₀)
  step-𝚝𝚎𝚜𝚝₀ :  ∀ {e : ⊢ 𝙽𝚊𝚝}                 → (stack ↑ 𝚝𝚎𝚜𝚝 e)                 ⇾  (stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e)
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
\end{code}

The relation ⇾ is (almost) total: for each non-final state there is a
follow-up state.

<<total>>
\begin{code}
data Final {Answer : Type} : State Answer → Set where
  final : ∀ {v : ⊨ Answer} → Final ([] ↓ v)

total : ∀ (s : State Answer) → ¬ Final s → ∃ (λ s′ → s ⇾ s′)
total (stack ↑ ` x) ¬final = stack ↓ x , step-`
total (stack ↑ 𝚒𝚏 x₁ 𝚝𝚑𝚎𝚗 x₂ 𝚎𝚕𝚜𝚎 x₃) ¬final = stack ∷ x₂ 𝚎𝚕𝚜𝚎 x₃ ↑ x₁ , step-𝚒𝚏
total (stack ↑ x₁ ⊞ x₂) ¬final = stack ∷ ◌ ⊞₀ x₂ ↑ x₁ , step-⊞₀
total (stack ↑ 𝚝𝚎𝚜𝚝 x₁) ¬final = stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ x₁ , step-𝚝𝚎𝚜𝚝₀
total ([] ↓ v) ¬final = ex-falso-quodlibet (¬final final)
total (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false) ¬final = stack ↑ e₂ , step-𝚎𝚕𝚜𝚎
total (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true) ¬final = stack ↑ e₁ , step-𝚝𝚑𝚎𝚗
total (stack ∷ ◌ ⊞₀ e₁ ↓ v) ¬final = stack ∷ v ⊞₁ ◌ ↑ e₁ , step-⊞₁
total (stack ∷ n₀ ⊞₁ ◌ ↓ v) ¬final = stack ↓ n₀ + v , step-⊞₂
total (stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ v) ¬final = stack ↓ test v , step-𝚝𝚎𝚜𝚝₁
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
complete : ∀ (stack : Stack Answer A) (e : ⊢ A) →
  ∀ (v : ⊨ A) → e ⇓ v → (stack ↑ e) ⇾⃰ (stack ↓ v)
complete stack (` v) _ (` v) = step step-` base
complete stack (𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) v (𝚒𝚏-𝚝𝚑𝚎𝚗 p₀ p₁ e₂) =
  proof
    (stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂)
  ⇾⟨ step-𝚒𝚏 ⟩
    stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↑ e₀
  ⇾⃰⟨ complete (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) e₀ true p₀ ⟩
    stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true
  ⇾⟨ step-𝚝𝚑𝚎𝚗  ⟩
    stack ↑ e₁
  ⇾⃰⟨ complete stack e₁ v p₁ ⟩
    (stack ↓ v)
  ∎
complete stack (𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) v (𝚒𝚏-𝚎𝚕𝚜𝚎 p₀ e₁ p₂) =
  proof
    (stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂)
  ⇾⟨ step-𝚒𝚏 ⟩
    stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↑ e₀
  ⇾⃰⟨ complete (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) e₀ false p₀ ⟩
    stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false
  ⇾⟨ step-𝚎𝚕𝚜𝚎 ⟩
    stack ↑ e₂
  ⇾⃰⟨ complete stack e₂ v p₂ ⟩
    (stack ↓ v)
  ∎
complete stack (e₀ ⊞ e₁) v (p₀ ⊞ p₁) =
  proof
    (stack ↑ e₀ ⊞ e₁)
  ⇾⟨ step-⊞₀ ⟩
    (stack ∷ ◌ ⊞₀ e₁ ↑ e₀)
  ⇾⃰⟨ complete (stack ∷ ◌ ⊞₀ e₁) e₀ _ p₀ ⟩
    (stack ∷ ◌ ⊞₀ e₁ ↓ _)
  ⇾⟨ step-⊞₁ ⟩
    (stack ∷ _ ⊞₁ ◌ ↑ e₁)
  ⇾⃰⟨ complete (stack ∷ _ ⊞₁ ◌) e₁ _ p₁ ⟩
    (stack ∷ _ ⊞₁ ◌ ↓ _)
  ⇾⟨ step-⊞₂ ⟩
    (stack ↓ v)
  ∎
complete stack (𝚝𝚎𝚜𝚝 e) v (𝚝𝚎𝚜𝚝 p) =
  proof
    (stack ↑ 𝚝𝚎𝚜𝚝 e)
  ⇾⟨ step-𝚝𝚎𝚜𝚝₀ ⟩
    (stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e)
  ⇾⃰⟨ complete (stack ∷ 𝚝𝚎𝚜𝚝 ◌) e _ p ⟩
    (stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ _)
  ⇾⟨ step-𝚝𝚎𝚜𝚝₁ ⟩
    stack ↓ v
  ∎

complete´ : ∀ (e : ⊢ A) (v : ⊨ A) →
  e ⇓ v → ∀ {s : Stack Answer A} → (s ↑ e) ⇾⃰ (s ↓ v)
complete´ e v p = complete _ e v p
\end{code}

\begin{code}
Total :  ∀ (e : ⊢ A) → ∃ (λ v → (stack ↑ e) ⇾⃰ (stack ↓ v))
Total e with ↓-total e
... | v , p = v , complete _ e v p
\end{code}

-------------------------------------------------------------------------------

apply : Stack Answer A → ⊢ A → ⊢ Answer
apply [] e = e
apply (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) e = apply stack (𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂)
apply (stack ∷ ◌ ⊞₀ e₁)    e = apply stack (e ⊞ e₁)
apply (stack ∷ v₀ ⊞₁ ◌)    e = apply stack (` v₀ ⊞ e)
apply (stack ∷ 𝚝𝚎𝚜𝚝 ◌)     e = apply stack (𝚝𝚎𝚜𝚝 e)

\begin{code}
_[_] : Stack Answer A → ⊢ A → ⊢ Answer
[]               [ e ] = e
(s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) [ e ] = s [ 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂ ]
(s ∷ ◌ ⊞₀ e₁)    [ e ] = s [ e ⊞ e₁ ]
(s ∷ v₀ ⊞₁ ◌)    [ e ] = s [ ` v₀ ⊞ e ]
(s ∷ 𝚝𝚎𝚜𝚝 ◌)     [ e ] = s [ 𝚝𝚎𝚜𝚝 e ]
\end{code}

zip : State Answer → ⊢ Answer
zip (stack ↓ v) = apply stack (` v)
zip (stack ↑ e) = apply stack e

\begin{code}
expr : State Answer → ⊢ Answer
expr (s ↓ v) = s [ ` v ]
expr (s ↑ e) = s [ e ]
\end{code}

-------------------------------------------------------------------------------

Correctness.  The proof below mimics the proof that small-step implies big-step.

\begin{code}
infix 2 _⪅_
_⪅_ : ⊢ A → ⊢ A → Set
e ⪅ e′  =  ∀ {v} → e ⇓ v → e′ ⇓ v  -- simulation / refinement

test-ctx : {e e′ : ⊢ 𝙽𝚊𝚝} → e ⪅ e′ → 𝚝𝚎𝚜𝚝 e ⪅ 𝚝𝚎𝚜𝚝 e′
test-ctx r (𝚝𝚎𝚜𝚝 p) = 𝚝𝚎𝚜𝚝 (r p)

plus-ctx₁ : {e e′ e₁ : ⊢ 𝙽𝚊𝚝} → e ⪅ e′ → e ⊞ e₁ ⪅ e′ ⊞ e₁
plus-ctx₁ r (p₁ ⊞ p₂) = r p₁ ⊞ p₂

plus-ctx₂ : {e e′ : ⊢ 𝙽𝚊𝚝} → e ⪅ e′ → ` n₀ ⊞ e ⪅ ` n₀ ⊞ e′
plus-ctx₂ r (p₁ ⊞ p₂) = p₁ ⊞ r p₂

if-ctx : {e e′ : ⊢ 𝙱𝚘𝚘𝚕} {e₁ e₂ : ⊢ A}  → e ⪅ e′ → 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂ ⪅ 𝚒𝚏 e′ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂
if-ctx r (𝚒𝚏-𝚝𝚑𝚎𝚗 p₀ p₁ e₂) = 𝚒𝚏-𝚝𝚑𝚎𝚗 (r p₀) p₁ e₂
if-ctx r (𝚒𝚏-𝚎𝚕𝚜𝚎 p₀ e₁ p₂) = 𝚒𝚏-𝚎𝚕𝚜𝚎 (r p₀) e₁ p₂

⪅-compositional : {e e′ : ⊢ A} → e ⪅ e′ → ∀ (s : Stack Answer A) → s [ e ] ⪅ s [ e′ ]
⪅-compositional r [] = r
⪅-compositional r (s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) = ⪅-compositional (if-ctx r) s
⪅-compositional r (s ∷ ◌ ⊞₀ e₁)    = ⪅-compositional (plus-ctx₁ r) s
⪅-compositional r (s ∷ n₀ ⊞₁ ◌)    = ⪅-compositional (plus-ctx₂ r) s
⪅-compositional r (s ∷ 𝚝𝚎𝚜𝚝 ◌)     = ⪅-compositional (test-ctx r) s
\end{code}

...............................................................................

\begin{code}
plus-refine : ` (n₀ + n₁) ⪅ ` n₀ ⊞ ` n₁
plus-refine (` _) = ` _ ⊞ ` _

test-refine : ` test n ⪅ 𝚝𝚎𝚜𝚝 (` n)
test-refine (` _) = 𝚝𝚎𝚜𝚝 (` _)

if-then-refine : {e₁ e₂ : ⊢ A} → e₁ ⪅ 𝚒𝚏 ` true 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂
if-then-refine p = 𝚒𝚏-𝚝𝚑𝚎𝚗 (` true)  p _

if-else-refine : {e₁ e₂ : ⊢ A} → e₂ ⪅ 𝚒𝚏 ` false 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂
if-else-refine p = 𝚒𝚏-𝚎𝚕𝚜𝚎 (` false) _ p
\end{code}

\begin{code}
step′ : ∀ {s s′ : State A} → s ⇾ s′ → expr s′ ⪅ expr s
step′ {s = stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true}  step-𝚝𝚑𝚎𝚗 p = ⪅-compositional if-then-refine stack p
step′ {s = stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false} step-𝚎𝚕𝚜𝚎 p = ⪅-compositional if-else-refine stack p
step′ {s = stack ∷ ◌ ⊞₀ e₁ ↓ n₀} step-⊞₁ p = p
step′ {s = stack ∷ n₀ ⊞₁ ◌ ↓ n₁} step-⊞₂ p = ⪅-compositional plus-refine stack p
step′ {s = stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ n} step-𝚝𝚎𝚜𝚝₁ p = ⪅-compositional test-refine stack p
step′ {s = stack ↑ ` v} step-` p = p
step′ {s = stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂} step-𝚒𝚏 p = p
step′ {s = stack ↑ e₀ ⊞ e₁} step-⊞₀ p = p
step′ {s = stack ↑ 𝚝𝚎𝚜𝚝 e} step-𝚝𝚎𝚜𝚝₀ p = p

identity : ∀ {A : Set} -> A -> A
identity a = a

step″ : ∀ s {s′ : State A} → s ⇾ s′ → expr s′ ⪅ expr s
step″ (s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true)  step-𝚝𝚑𝚎𝚗 = ⪅-compositional if-then-refine s
step″ (s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false) step-𝚎𝚕𝚜𝚎 = ⪅-compositional if-else-refine s
step″ (s ∷ ◌ ⊞₀ e₁ ↓ n₀) step-⊞₁ = identity
step″ (s ∷ n₀ ⊞₁ ◌ ↓ n₁) step-⊞₂ = ⪅-compositional plus-refine s
step″ (s ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ n) step-𝚝𝚎𝚜𝚝₁ = ⪅-compositional test-refine s
step″ (s ↑ ` v) step-` = identity
step″ (s ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) step-𝚒𝚏 = identity
step″ (s ↑ e₀ ⊞ e₁) step-⊞₀ = identity
step″ (s ↑ 𝚝𝚎𝚜𝚝 e) step-𝚝𝚎𝚜𝚝₀ = identity
\end{code}

\begin{code}
simulateᴿ : ∀ {s s′ : State A} → s ⇾⃰ s′ → expr s′ ⪅ expr s
simulateᴿ (base)      q = q
-- simulateᴿ (step p ps) q = step″ _ p (simulateᴿ ps q)
simulateᴿ (step p ps) q = step′ p (simulateᴿ ps q)

correct : ∀ {e : ⊢ A} {v : ⊨ A} → ([] ↑ e ⇾⃰ [] ↓ v) → e ⇓ v
correct p = simulateᴿ p (` _)
\end{code}

-------------------------------------------------------------------------------
