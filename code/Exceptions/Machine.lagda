Abstract machine for the arithmetic language with exceptions.

The machine operates in three modes:
  ↑  eval mode   : evaluating an expression
  ↓  return mode : returning a value
  ☇  exn mode    : unwinding the stack looking for a catch frame

\begin{code}
module Exceptions.Machine where

open import Exceptions.Definitions public
open import Exceptions.Big-Step     public

open import Data.Nat
open import Data.Bool hiding (T; if_then_else_) renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; sym; subst) renaming (refl to reflexive)
open import Data.Product using (∃) renaming (_,_ to _﹐_)
open import Data.Empty using (⊥) renaming (⊥-elim to ex-falso)

infix  10 ⊢_↑_ ⊢_↓_ ⊢_☇_
infixr 60 _∷_
infix   5 _⇾_ _⇾⃰_
infix  70 _⊞₀_ _⊞₁_ _𝚎𝚕𝚜𝚎_
\end{code}

Holes, frames, and stacks.

\begin{code}
data Hole : Set where
    ◌ : Hole

-- Frame A B  =  an expression of type A  with a hole of type B
data Frame : Type → Type → Set where
    _𝚎𝚕𝚜𝚎_  : ⊢ T → ⊢ T → Frame T Bool         
    _⊞₀_    : Hole → ⊢ Nat → Frame Nat Nat     
    _⊞₁_    : ⊨ Nat → Hole → Frame Nat Nat     
    test    : Hole → Frame Bool Nat            
    catch   : (Exception → ⊢ T) → Frame T T 

data Stack (Answer : Type) : Type → Set where
    []  : Stack Answer Answer
    _∷_ : Stack Answer T₁ → Frame T₁ T₂ → Stack Answer T₂
\end{code}

Machine states.

\begin{code}
data State (Answer : Type) : Set where
    ⊢_↑_ : Stack Answer T → ⊢ T      → State Answer
    ⊢_↓_ : Stack Answer T → ⊨ T      → State Answer
    ⊢_☇_ : Stack Answer T → Exception → State Answer

private variable
    Answer : Type
    stack  : Stack Answer T
    s s₀ s₁ s₂ : State Answer
\end{code}

Transition relation.

\begin{code}
data _⇾_ : State Answer → State Answer → Set where
    step-`      : ∀ {T : Type} {stk : Stack Answer T} {v : ⊨ T}
                → ⊢ stk ↑ ` v ⇾ ⊢ stk ↓ v

    step-⊞      : ⊢ stack ↑ (e₁ ⊞ e₂)
                ⇾ ⊢ stack ∷ (◌ ⊞₀ e₂) ↑ e₁

    step-test   : ⊢ stack ↑ test e
                ⇾ ⊢ stack ∷ test ◌ ↑ e

    step-if     : ⊢ stack ↑ (if e then e₁ else e₂)
                ⇾ ⊢ stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↑ e

    step-throw  : ⊢ stack ↑ throw ex ⇾ ⊢ stack ☇ ex

    step-try    : ∀ {T : Type} {stk : Stack Answer T} {e : ⊢ T} {h : Exception → ⊢ T}
                → ⊢ stk ↑ (try e catch h)
                ⇾ ⊢ stk ∷ catch h ↑ e

    step-⊞₁    : ⊢ stack ∷ (◌ ⊞₀ e₂) ↓ v₁
                ⇾ ⊢ stack ∷ (v₁ ⊞₁ ◌) ↑ e₂

    step-⊞₂    : ⊢ stack ∷ (v₁ ⊞₁ ◌) ↓ v₂
                ⇾ ⊢ stack ↓ (v₁ + v₂)

    step-test₁  : ⊢ stack ∷ test ◌ ↓ n
                ⇾ ⊢ stack ↓ test' n

    step-𝚝𝚑𝚎𝚗   : ⊢ stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↓ true
                ⇾ ⊢ stack ↑ e₁

    step-𝚎𝚕𝚜𝚎   : ⊢ stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↓ false
                ⇾ ⊢ stack ↑ e₂

    step-catch-ok : ∀ {T : Type} {stk : Stack Answer T} {v : ⊨ T} {h : Exception → ⊢ T}
                  → ⊢ stk ∷ catch h ↓ v
                  ⇾ ⊢ stk ↓ v

    -- Exception mode: unwind frames until a handler is found.
    -- step-discard : ∀ {T : Type} {stk : Stack Answer T₁} {ex : Exception} {f : Frame T₁ T₂}
    --             → ⊢ stk ∷ f ☇ ex
    --             ⇾ ⊢ stk ☇ ex

    step-drop-𝚎𝚕𝚜𝚎 : ⊢ stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ☇ ex ⇾ ⊢ stack ☇ ex

    step-drop-⊞₀   : ⊢ stack ∷ (◌ ⊞₀ e₂) ☇ ex   ⇾ ⊢ stack ☇ ex

    step-drop-⊞₁   : ⊢ stack ∷ (v₁ ⊞₁ ◌) ☇ ex   ⇾ ⊢ stack ☇ ex

    step-drop-test  : ⊢ stack ∷ test ◌ ☇ ex        ⇾ ⊢ stack ☇ ex

    step-catch-exn  : ⊢ stack ∷ catch h ☇ ex      ⇾ ⊢ stack ↑ h ex
\end{code}

Reflexive-transitive closure.

\begin{code}
data _⇾⃰_ : State Answer → State Answer → Set where
    base : s ⇾⃰ s
    step : s₀ ⇾ s₁ → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₂

⇾⃰-transitive : ∀ {s₀ s₁ s₂ : State Answer}
    → s₀ ⇾⃰ s₁ → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₂
⇾⃰-transitive base      q = q
⇾⃰-transitive (step p r) q = step p (⇾⃰-transitive r q)
\end{code}

Completeness: the machine reaches ⊢ [] ↓ v if e ⇓ v, and ⊢ stk ☇ ex if e ⇑ ex.
The two lemmas are mutually recursive (try-catch needs both).

\begin{code}
mutual

 complete : ∀ (e : ⊢ T) (v : ⊨ T) (stk : Stack Answer T)
    → e ⇓ v
    → (⊢ stk ↑ e) ⇾⃰ (⊢ stk ↓ v)
 complete (` _) v stk (` .v) =
    step step-` base

 complete (e₁ ⊞ e₂) _ stk (_⊞_ {n₁ = n₁} {n₂ = n₂} p₁ p₂) =
    step step-⊞
    (⇾⃰-transitive (complete e₁ n₁ (stk ∷ ◌ ⊞₀ e₂) p₁)
    (step step-⊞₁
    (⇾⃰-transitive (complete e₂ n₂ (stk ∷ n₁ ⊞₁ ◌) p₂)
    (step step-⊞₂ base))))

 complete (test e) _ stk (test p) =
    step step-test
    (⇾⃰-transitive (complete e _ (stk ∷ test ◌) p)
    (step step-test₁ base))

 complete (if e then e₁ else e₂) v stk (if-then pe p₁) =
    step step-if
    (⇾⃰-transitive (complete e _ (stk ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) pe)
    (step step-𝚝𝚑𝚎𝚗
    (complete e₁ v stk p₁)))

 complete (if e then e₁ else e₂) v stk (if-else pe p₂) =
    step step-if
    (⇾⃰-transitive (complete e _ (stk ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) pe)
    (step step-𝚎𝚕𝚜𝚎
    (complete e₂ v stk p₂)))

 complete (try e catch h) v stk (try-return p) =
    step step-try
    (⇾⃰-transitive (complete e v (stk ∷ catch h) p)
    (step step-catch-ok base))

 complete (try e catch h) v stk (try-catch {ex = ex} pe ph) =
    step step-try
    (⇾⃰-transitive (complete-exn e ex (stk ∷ catch h) pe)
    (step step-catch-exn
    (complete (h ex) v stk ph)))

 -- Exception completeness: if e ⇑ ex then the machine reaches ⊢ stk ☇ ex.

 complete-exn : ∀ (e : ⊢ T) (ex : Exception) (stk : Stack Answer T)
    → e ⇑ ex
    → (⊢ stk ↑ e) ⇾⃰ (⊢ stk ☇ ex)
 complete-exn (throw _) ex stk throw-rule =
    step step-throw base

 complete-exn (e₁ ⊞ e₂) ex stk (⊞-exn₁ p₁) =
    step step-⊞
    (⇾⃰-transitive (complete-exn e₁ ex (stk ∷ (◌ ⊞₀ e₂)) p₁)
    (step step-drop-⊞₀ base))

 complete-exn (e₁ ⊞ e₂) ex stk (⊞-exn₂ p₁ p₂) =
    step step-⊞
    (⇾⃰-transitive (complete e₁ _ (stk ∷ (◌ ⊞₀ e₂)) p₁)
    (step step-⊞₁
    (⇾⃰-transitive (complete-exn e₂ ex (stk ∷ (_ ⊞₁ ◌)) p₂)
    (step step-drop-⊞₁ base))))

 complete-exn (test e) ex stk (test-raise p) =
    step step-test
    (⇾⃰-transitive (complete-exn e ex (stk ∷ test ◌) p)
    (step step-drop-test base))

 complete-exn (if e then e₁ else e₂) ex stk (if-raise p) =
    step step-if
    (⇾⃰-transitive (complete-exn e ex (stk ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) p)
    (step step-drop-𝚎𝚕𝚜𝚎 base))

 complete-exn (if e then e₁ else e₂) ex stk (if-then pe p₁) =
    step step-if
    (⇾⃰-transitive (complete e _ (stk ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) pe)
    (step step-𝚝𝚑𝚎𝚗
    (complete-exn e₁ ex stk p₁)))

 complete-exn (if e then e₁ else e₂) ex stk (if-else pe p₂) =
    step step-if
    (⇾⃰-transitive (complete e _ (stk ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) pe)
    (step step-𝚎𝚕𝚜𝚎
    (complete-exn e₂ ex stk p₂)))

 complete-exn (try e catch h) ex stk (try-catch pe ph) =
    step step-try
    (⇾⃰-transitive (complete-exn e _ (stk ∷ catch h) pe)
    (step step-catch-exn
    (complete-exn (h _) ex stk ph)))
\end{code}

\begin{code}
-- Single-step determinism.
det : ∀ {Answer : Type} {s₀ s₁ s₂ : State Answer} → s₀ ⇾ s₁ → s₀ ⇾ s₂ → s₁ ≡ s₂
det step-`         step-`         = reflexive
det step-⊞         step-⊞         = reflexive
det step-test      step-test      = reflexive
det step-if        step-if        = reflexive
det step-throw     step-throw     = reflexive
det step-try       step-try       = reflexive
det step-⊞₁        step-⊞₁        = reflexive
det step-⊞₂        step-⊞₂        = reflexive
det step-test₁     step-test₁     = reflexive
det step-𝚝𝚑𝚎𝚗      step-𝚝𝚑𝚎𝚗      = reflexive
det step-𝚎𝚕𝚜𝚎      step-𝚎𝚕𝚜𝚎      = reflexive
det step-catch-ok  step-catch-ok  = reflexive
det step-drop-𝚎𝚕𝚜𝚎 step-drop-𝚎𝚕𝚜𝚎 = reflexive
det step-drop-⊞₀   step-drop-⊞₀   = reflexive
det step-drop-⊞₁   step-drop-⊞₁   = reflexive
det step-drop-test step-drop-test = reflexive
det step-catch-exn step-catch-exn = reflexive

-- ⊢ [] ↓ v and ⊢ [] ☇ ex are both final (stuck) states.
stuck-↓ : ∀ {T : Type} {v : ⊨ T} {s : State T} → (⊢ [] ↓ v) ⇾ s → ⊥
stuck-↓ ()

stuck-☇ : ∀ {T : Type} {ex : Exception} {s : State T} → (⊢ [] ☇ ex) ⇾ s → ⊥
stuck-☇ ()

confluence : ∀ {Answer : Type} {s s₁ s₂ : State Answer}
    → s ⇾⃰ s₁ → s ⇾⃰ s₂
    → ({s' : State Answer} → s₁ ⇾ s' → ⊥)
    → ({s' : State Answer} → s₂ ⇾ s' → ⊥)
    → s₁ ≡ s₂
confluence base           base           _   _   = reflexive
confluence base           (step r _)     ns₁ _   = ex-falso (ns₁ r)
confluence (step r _)     base           _   ns₂ = ex-falso (ns₂ r)
confluence (step r₁ tr₁) (step r₂ tr₂) ns₁ ns₂ rewrite det r₁ r₂ =
    confluence tr₁ tr₂ ns₁ ns₂

-- Injectivity of the two final-state constructors.
↓-inj : ∀ {Answer : Type} {v₁ v₂ : ⊨ Answer}
    → _≡_ {A = State Answer} (⊢ [] ↓ v₁) (⊢ [] ↓ v₂) → v₁ ≡ v₂
↓-inj reflexive = reflexive

☇-inj : ∀ {Answer : Type} {ex₁ ex₂ : Exception}
    → _≡_ {A = State Answer} (⊢ [] ☇ ex₁) (⊢ [] ☇ ex₂) → ex₁ ≡ ex₂
☇-inj reflexive = reflexive

-- The two constructors are disjoint.
↓≢☇ : ∀ {Answer : Type} {v : ⊨ Answer} {ex : Exception}
    → _≡_ {A = State Answer} (⊢ [] ↓ v) (⊢ [] ☇ ex) → ⊥
↓≢☇ ()

-- Correctness: a machine run ⊢ [] ↑ e ⇾⃰ ⊢ [] ↓ v implies e ⇓ v.
-- Proof: totality gives r. If r = return v', completeness gives a canonical run;
-- confluence yields v' = v. If r = raise ex, completeness-exn gives a run to ☇;
-- confluence with the ↓ run yields an absurdity (distinct constructors).
correct : ∀ (e : ⊢ T) (v : ⊨ T)
    → (⊢ [] ↑ e) ⇾⃰ (⊢ [] ↓ v)
    → e ⇓ v
correct e v tr with total e
... | return v' ﹐ p =
    let tr' : ⊢ [] ↑ e ⇾⃰ ⊢ [] ↓ v'
        tr' = complete e v' [] p

        eq : (⊢ [] ↓ v') ≡ (⊢ [] ↓ v)
        eq  = confluence tr' tr stuck-↓ stuck-↓
    in  subst (λ u → e ⇓ u) (↓-inj eq) p
... | raise ex ﹐ p =
    let tr' : ⊢ [] ↑ e ⇾⃰ ⊢ [] ☇ ex
        tr' = complete-exn e ex [] p

        eq : ⊢ [] ☇ ex ≡ ⊢ [] ↓ v
        eq  = confluence tr' tr stuck-☇ stuck-↓
    in  ex-falso (↓≢☇ (sym eq))

-- Correctness for the exception outcome: ⊢ [] ↑ e ⇾⃰ ⊢ [] ☇ ex implies e ⇑ ex.
correct-exn : ∀ (e : ⊢ T) (ex : Exception)
    → (⊢ [] ↑ e) ⇾⃰ (⊢ [] ☇ ex)
    → e ⇑ ex
correct-exn e ex tr with total e
... | return v ﹐ p =
    let tr' : ⊢ [] ↑ e ⇾⃰ ⊢ [] ↓ v
        tr' = complete e v [] p
        eq : ⊢ [] ↓ v ≡ ⊢ [] ☇ ex
        eq  = confluence tr' tr stuck-↓ stuck-☇
    in  ex-falso (↓≢☇ eq)
... | raise ex' ﹐ p =
    let tr' : ⊢ [] ↑ e ⇾⃰ ⊢ [] ☇ ex'
        tr' = complete-exn e ex' [] p

        eq : ⊢ [] ☇ ex' ≡ ⊢ [] ☇ ex
        eq  = confluence tr' tr stuck-☇ stuck-☇
    in  subst (e ⇑_) (☇-inj eq) p
\end{code}
