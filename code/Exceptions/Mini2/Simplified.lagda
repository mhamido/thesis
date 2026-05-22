A small-step machine for Mini.

correctness:   ([] ↑ e) ⇾⃰ ([] ↓ v)  →  e ⇓ v
completeness:  e ⇓ v  →  ([] ↑ e) ⇾⃰ ([] ↓ v)

%------------------------------------------------------------------------------

\begin{code}
-- {-# OPTIONS --safe --without-K #-}
{-# OPTIONS --without-K #-}

module Simplified where

open import Mini2
  hiding (deterministic; Frame; Stack; State; {- base; -} step)
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
infix  120 _𝚎𝚕𝚜𝚎_
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
  _catch_ : Hole → ⊢ A → Frame A A
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
●  _↯: exception mode (unravelling the stack, searching for a handler).

\begin{code}
data State (Answer : Type) : Set where
  _↑_ : Stack Answer A → ⊢ A → State Answer
  _↓_ : Stack Answer A → ⊨ A → State Answer
  _↯  : Stack Answer A → State Answer
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
next (stack ∷ ◌ catch x₂   ↓ v) = stack ↓ v

next (stack ↑ ` v)                   = stack ↓ v
next (stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) = stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↑ e₀
next (stack ↑ e₀ ⊞ e₁)               = stack ∷ (◌ ⊞₀ e₁) ↑ e₀
next (stack ↑ 𝚝𝚎𝚜𝚝 e)                = stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e
next (stack ↑ throw) = stack ↯
next (stack ↑ try x₁ catch x₂) = stack ∷ (◌ catch x₂) ↑ x₁

next ([] ↯) = [] ↯
next (stack ∷ (x 𝚎𝚕𝚜𝚎 x₁) ↯) = stack ↯
next (stack ∷ (x ⊞₀ x₁) ↯) = stack ↯
next (stack ∷ (x ⊞₁ x₁) ↯) = stack ↯
next (stack ∷ 𝚝𝚎𝚜𝚝 x ↯) = stack ↯
next (stack ∷ (◌ catch h) ↯) = stack ↑ h
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
  step-𝚒𝚏    :  ∀ {e₀ : ⊢ 𝙱𝚘𝚘𝚕} {e₁ e₂ : ⊢ A} → (stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂)   ⇾  (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↑ e₀)
  step-⊞₀    :  ∀ {e₀ e₁ : ⊢ 𝙽𝚊𝚝}             → (stack ↑ e₀ ⊞ e₁)                ⇾  (stack ∷ (◌ ⊞₀ e₁) ↑ e₀)
  step-𝚝𝚎𝚜𝚝₀ :  ∀ {e : ⊢ 𝙽𝚊𝚝}                 → (stack ↑ 𝚝𝚎𝚜𝚝 e)                 ⇾  (stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e)

  step-throw : (stack ↑ throw) ⇾ (stack ↯)
  {- This would be ideal, but currently causes quite the headache with the types...
  step-drop  : ∀ {A B : Type} {stack : Stack B _}  {x : Frame A A} (h : ∀ {h : ⊢ A} → ¬(x ≡ (◌ catch h)))
             → (stack ∷ x ↯) ⇾ (stack ↯)
  -}

  step-drop₁ : ∀ {e₁ e₂ : ⊢ A} → ((stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) ↯) ⇾ (stack ↯)
  step-drop₂ : ∀ {e₂ : ⊢ 𝙽𝚊𝚝} → (stack ∷ ◌ ⊞₀ e₂ ↯) ⇾ (stack ↯)
  step-drop₃ : ∀ {v₁ : ⊨ 𝙽𝚊𝚝} → (stack ∷ v₁ ⊞₁ ◌ ↯) ⇾ (stack ↯)
  step-drop₄ : (stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↯) ⇾ (stack ↯)
  -- todo: the rest
  
  step-try   : ∀ {e₁ e₂ : ⊢ A} → (stack ↑ try e₁ catch e₂) ⇾ (stack ∷ ◌ catch e₂ ↑ e₁)
  step-exn   : ∀ {h : ⊢ A} → (stack ∷ ◌ catch h ↯) ⇾ (stack ↑ h)
  step-ok    : ∀ {h : ⊢ A} {v : ⊨ A} → (stack ∷ ◌ catch h ↓ v) ⇾ (stack ↓ v) 
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
deterministic step-throw step-throw = reflexive
deterministic step-drop₁ step-drop₁ = reflexive
deterministic step-drop₂ step-drop₂ = reflexive
deterministic step-drop₃ step-drop₃ = reflexive
deterministic step-drop₄ step-drop₄ = reflexive
deterministic step-try step-try = reflexive
deterministic step-exn step-exn = reflexive
deterministic step-ok step-ok = reflexive
\end{code}

The relation ⇾ is (almost) total: for each non-final state there is a
follow-up state.

<<total>>
\begin{code}
data Final {Answer : Type} : State Answer → Set where
  final₁ : ∀ {v : ⊨ Answer} → Final ([] ↓ v)
  final₂ : Final ([] ↯) 

total : ∀ (s : State Answer) → ¬ Final s → ∃ (λ s′ → s ⇾ s′)
total (stack ↑ ` x) ¬final = stack ↓ x , step-`
total (stack ↑ 𝚒𝚏 x₁ 𝚝𝚑𝚎𝚗 x₂ 𝚎𝚕𝚜𝚎 x₃) ¬final = stack ∷ x₂ 𝚎𝚕𝚜𝚎 x₃ ↑ x₁ , step-𝚒𝚏
total (stack ↑ x₁ ⊞ x₂) ¬final = stack ∷ ◌ ⊞₀ x₂ ↑ x₁ , step-⊞₀
total (stack ↑ 𝚝𝚎𝚜𝚝 x₁) ¬final = stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ x₁ , step-𝚝𝚎𝚜𝚝₀
total ([] ↓ v) ¬final = ex-falso-quodlibet (¬final final₁)
total (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false) ¬final = stack ↑ e₂ , step-𝚎𝚕𝚜𝚎
total (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true) ¬final = stack ↑ e₁ , step-𝚝𝚑𝚎𝚗
total (stack ∷ ◌ ⊞₀ e₁ ↓ v) ¬final = stack ∷ v ⊞₁ ◌ ↑ e₁ , step-⊞₁
total (stack ∷ n₀ ⊞₁ ◌ ↓ v) ¬final = stack ↓ n₀ + v , step-⊞₂
total (stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ v) ¬final = stack ↓ test v , step-𝚝𝚎𝚜𝚝₁
total (stack ↑ throw) ¬final = (stack ↯) , step-throw
total (stack ↑ try x₁ catch x₂) ¬final = stack ∷ ◌ catch x₂ ↑ x₁ , step-try
total (stack ∷ ◌ catch h ↓ v) ¬final = stack ↓ v , step-ok
total ([] ↯) ¬final = ex-falso-quodlibet (¬final final₂)
total ((stack ∷ (x 𝚎𝚕𝚜𝚎 x₁)) ↯) ¬final = (stack ↯) , step-drop₁
total ((stack ∷ ◌ ⊞₀ x₁) ↯) ¬final = (stack ↯) , step-drop₂
total ((stack ∷ x ⊞₁ ◌) ↯) ¬final = (stack ↯) , step-drop₃
total ((stack ∷ 𝚝𝚎𝚜𝚝 ◌) ↯) ¬final = (stack ↯) , step-drop₄
total ((stack ∷ (◌ catch x₁)) ↯) ¬final = stack ↑ x₁ , step-exn
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
mutual
  unwind : ∀ (s : Stack Answer A) (e : ⊢ A) → (e ⇑) → (s ↑ e) ⇾⃰ (s ↯)
  unwind stack e throw-error = step step-throw base
  unwind stack (e₁ ⊞ e₂) (_⊞₁_ e⇑) =
    proof
      stack ↑ _ ⊞ _
    ⇾⟨ step-⊞₀ ⟩
      stack ∷ ◌ ⊞₀ e₂ ↑ e₁
    ⇾⃰⟨ unwind (stack ∷ ◌ ⊞₀ e₂) e₁ e⇑ ⟩
      ((stack ∷ ◌ ⊞₀ e₂) ↯)
    ⇾⟨ step-drop₂ ⟩
      (stack ↯)
    ∎

  unwind stack (e₁ ⊞ e₂) (_⊞₂_ {v₁ = v₁} p₁ p₂) =
      proof
        stack ↑ e₁ ⊞ e₂
      ⇾⟨ step-⊞₀ ⟩
        stack ∷ ◌ ⊞₀ e₂ ↑ e₁
      ⇾⃰⟨ complete (stack ∷ ◌ ⊞₀ e₂) e₁ v₁ p₁ ⟩
        stack ∷ ◌ ⊞₀ e₂ ↓ v₁  
      ⇾⟨ step-⊞₁ ⟩
        stack ∷ v₁ ⊞₁ ◌ ↑ e₂
      ⇾⃰⟨ unwind (stack ∷ v₁ ⊞₁ ◌) e₂ p₂ ⟩
        (stack ∷ v₁ ⊞₁ ◌) ↯
      ⇾⟨ step-drop₃ ⟩
        (stack ↯)
      ∎
    
  unwind stack (𝚒𝚏 c 𝚝𝚑𝚎𝚗 t 𝚎𝚕𝚜𝚎 e) (𝚒𝚏₁ p e₃ e₄) =
    proof
      stack ↑ 𝚒𝚏 c 𝚝𝚑𝚎𝚗 t 𝚎𝚕𝚜𝚎 e
    ⇾⟨ step-𝚒𝚏 ⟩
      stack ∷ (t 𝚎𝚕𝚜𝚎 e) ↑ c
    ⇾⃰⟨ unwind (stack ∷ (t 𝚎𝚕𝚜𝚎 e)) c p ⟩
      ((stack ∷ (t 𝚎𝚕𝚜𝚎 e)) ↯)
    ⇾⟨ step-drop₁ ⟩
      (stack ↯)
    ∎
      
  unwind stack (𝚒𝚏 c 𝚝𝚑𝚎𝚗 t 𝚎𝚕𝚜𝚎 e) (𝚒f₂ p₀ p e₃) =
    proof
      stack ↑ 𝚒𝚏 c 𝚝𝚑𝚎𝚗 t 𝚎𝚕𝚜𝚎 e
    ⇾⟨ step-𝚒𝚏 ⟩
      stack ∷ (t 𝚎𝚕𝚜𝚎 e) ↑ c
    ⇾⃰⟨ complete (stack ∷ (t 𝚎𝚕𝚜𝚎 e)) c true p₀ ⟩
      stack ∷ (t 𝚎𝚕𝚜𝚎 e) ↓ true
    ⇾⟨ step-𝚝𝚑𝚎𝚗 ⟩
      stack ↑ t
    ⇾⃰⟨ unwind stack t p ⟩
      (stack ↯)
    ∎
  
  unwind stack (𝚒𝚏 c 𝚝𝚑𝚎𝚗 t 𝚎𝚕𝚜𝚎 e) (𝚒𝚏₃ p₀ e₃ p) =
    proof
      stack ↑ 𝚒𝚏 c 𝚝𝚑𝚎𝚗 t 𝚎𝚕𝚜𝚎 e
    ⇾⟨ step-𝚒𝚏 ⟩
      stack ∷ (t 𝚎𝚕𝚜𝚎 e) ↑ c
    ⇾⃰⟨ complete _ c false p₀ ⟩
      stack ∷ (t 𝚎𝚕𝚜𝚎 e) ↓ false
    ⇾⟨ step-𝚎𝚕𝚜𝚎 ⟩
      stack ↑ e
    ⇾⃰⟨ unwind stack e p ⟩
      (stack ↯)
    ∎

  unwind stack (𝚝𝚎𝚜𝚝 e) (𝚝𝚎𝚜𝚝-error p) =
    proof
      stack ↑ 𝚝𝚎𝚜𝚝 e
    ⇾⟨ step-𝚝𝚎𝚜𝚝₀ ⟩
      (stack ∷ 𝚝𝚎𝚜𝚝 ◌) ↑ e
    ⇾⃰⟨ unwind (stack ∷ 𝚝𝚎𝚜𝚝 ◌) e p ⟩
      ((stack ∷ 𝚝𝚎𝚜𝚝 ◌) ↯)
    ⇾⟨ step-drop₄ ⟩
      (stack ↯)
    ∎
    
  unwind stack (try e catch h) (try-rethrow p₀ p₁) =
    proof
      stack ↑ try e catch h
    ⇾⟨ step-try ⟩
      stack ∷ ◌ catch h ↑ e
    ⇾⃰⟨ unwind (stack ∷ (◌ catch h)) e p₀ ⟩
      stack ∷ (◌ catch h) ↯
    ⇾⟨ step-exn ⟩
      stack ↑ h
    ⇾⃰⟨ unwind stack h p₁ ⟩
      stack ↯
    ∎

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

  complete stack throw v ()

  complete stack (try e₁ catch e₂) v (try-ok p₀ p₁) =
    proof
      stack ↑ (try e₁ catch e₂)
    ⇾⟨ step-try ⟩
      stack ∷ (◌ catch e₂) ↑ e₁
    ⇾⃰⟨ complete _ e₁ v p₀ ⟩
      stack ∷ (◌ catch e₂) ↓ v
    ⇾⟨ step-ok ⟩
      stack ↓ v
    ∎

  complete stack (try e₁ catch e₂) v (try-catch p₀ p₁) =
    proof
      stack ↑ try e₁ catch e₂
    ⇾⟨ step-try ⟩
      stack ∷ (◌ catch e₂) ↑ e₁
    ⇾⃰⟨ unwind _ e₁ p₀ ⟩
      stack ∷ (◌ catch e₂) ↯
    ⇾⟨ step-exn ⟩
      stack ↑ e₂
    ⇾⃰⟨ complete stack e₂ v p₁ ⟩
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
(s ∷ ◌ catch h)  [ e ] = s [ try e catch h ]
\end{code}

zip : State Answer → ⊢ Answer
zip (stack ↓ v) = apply stack (` v)
zip (stack ↑ e) = apply stack e

\begin{code}
expr : State Answer → ⊢ Answer
expr (s ↓ v) = s [ ` v ]
expr (s ↑ e) = s [ e ]
expr (s ↯) = s [ throw ]
\end{code}

-------------------------------------------------------------------------------

Correctness.  The proof below mimics the proof that small-step implies big-step.

\begin{code}
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

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

try-ctx₂ : {e h h′ : ⊢ A} → (e ⇑) → h ⪅ h′ → try e catch h ⪅ try e catch h′ 
try-ctx₂ e⇑ r (try-ok p e₂) = ex-falso-quodlibet (discriminate p e⇑)
try-ctx₂ e⇑ r (try-catch x p) = try-catch e⇑ (r p)

-- try-ctx₁ : {e e′ h : ⊢ A} → e ⪅₂ e′ → try e catch h ⪅ try e′ catch h
-- try-ctx₁ r (try-ok p e₂) = {!!}
-- try-ctx₁ r (try-catch x p) = try-catch {!!} p -- this is where we need to modify the refines to relation.

-- Recall that the language is total, i.e: ∀ e → (∃ v → e ⇓ v) ⊎ (e ⇑).
infix 2 _⪅₂_
_⪅₂_ : ⊢ A → ⊢ A → Set
e₁ ⪅₂ e₂ = (e₁ ⪅ e₂) × ((e₁ ⇑) → (e₂ ⇑))

try-ctx : {e e′ h : ⊢ A} → e ⪅₂ e′ → try e catch h ⪅ try e′ catch h
try-ctx (r₁ , r₂) (try-ok p e₂) = try-ok (r₁ p) e₂
try-ctx (r₁ , r₂) (try-catch x p) = try-catch (r₂ x) p

private variable
  e₁ e₂ : ⊢ A
  -- C : Frame _ A

mutual
  ⪅-compositional : {e e′ : ⊢ A} → e ⪅ e′ → ∀ (s : Stack Answer A) → s [ e ] ⪅ s [ e′ ]
  ⪅-compositional r [] = r
  ⪅-compositional r (s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) = ⪅-compositional (if-ctx r) s
  ⪅-compositional r (s ∷ ◌  ⊞₀ e₁)   = ⪅-compositional (plus-ctx₁ r) s
  ⪅-compositional r (s ∷ n₀ ⊞₁  ◌)   = ⪅-compositional (plus-ctx₂ r) s
  ⪅-compositional r (s ∷    𝚝𝚎𝚜𝚝 ◌)  = ⪅-compositional (test-ctx r) s
  ⪅-compositional r (s ∷ ◌ catch h)  = ⪅-compositional (try-ctx (r , {!!})) s

  ⪅-exceptional : {e e‵ : ⊢ A} → (e ⇑ → e‵ ⇑) → ∀ (s : Stack Answer A) → s [ e ] ⪅ s [ e‵ ]
  ⪅-exceptional p s st = {! st  !}

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

try-refine : {e : ⊢ A} (h : ⊢ A) → e ⪅ try e catch h
try-refine h p = try-ok p h

catch-refine : {e h : ⊢ A} → (e ⇑) → h ⪅ try e catch h
catch-refine e⇑ p = try-catch e⇑ p
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
step′ {s = s} step-throw p = p
step′ {s = (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) ↯} step-drop₁ p = ⪅-compositional (λ ()) stack p
step′ {s = (stack ∷ ◌ ⊞₀ e₂) ↯} step-drop₂ p = ⪅-compositional (λ ()) stack p
step′ {s = (stack ∷ v₁ ⊞₁ ◌) ↯} step-drop₃ p = ⪅-compositional (λ ()) stack p
step′ {s = (stack ∷ 𝚝𝚎𝚜𝚝 ◌) ↯} step-drop₄ p = ⪅-compositional (λ ()) stack p
step′ {s = s} step-try p = p
step′ {s = (stack ∷ (◌ catch h)) ↯} step-exn p = ⪅-compositional (catch-refine throw-error) stack p
step′ {s = stack ∷ (◌ catch h) ↓ v} step-ok p = ⪅-compositional (try-refine h) stack p

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
step″ (s ↑ _) step-throw = identity
step″ (s ↑ _) step-try = identity
step″ (s ∷ (◌ catch h) ↓ v) step-ok = ⪅-compositional (try-refine h) s
step″ (s ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↯) step-drop₁ = ⪅-compositional (λ ()) s
step″ (s ∷ ◌ ⊞₀ e₂ ↯) step-drop₂ = ⪅-compositional (λ ()) s
step″ (s ∷ v₁ ⊞₁ ◌ ↯) step-drop₃ = ⪅-compositional (λ ()) s
step″ (s ∷ 𝚝𝚎𝚜𝚝 ◌ ↯) step-drop₄ = ⪅-compositional (λ ()) s
step″ (s ∷ ◌ catch h ↯) step-exn = ⪅-compositional (catch-refine throw-error) s
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

