\begin{code}
module Arith.Machine where

open import Arith.Definitions public
open import Arith.Big-Step public

open import Data.Nat
open import Data.Bool hiding (T; if_then_else_) renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; subst) renaming (refl to reflexive)
open import Data.Product using (∃) renaming (_,_ to _﹐_)
open import Data.Empty using (⊥; ⊥-elim)

infix 10 ⊢_↑_
infixr 60 _∷_
infix 5 _⇾_ _⇾⃰_
infix 70 _⊞₀_ _⊞₁_ _𝚎𝚕𝚜𝚎_
\end{code}

\begin{code}
data Hole : Set where
    ◌ : Hole

data Frame : Type → Type → Set where
    _𝚎𝚕𝚜𝚎_  : ⊢ T → ⊢ T → Frame T Bool
    _⊞₀_    : Hole → ⊢ Nat → Frame Nat Nat
    _⊞₁_    : ⊨ Nat → Hole → Frame Nat Nat
    test    : Hole → Frame Bool Nat

data Stack (Answer : Type) : Type → Set where
    []     : Stack Answer Answer
    _∷_    : Stack Answer T₁ → Frame T₁ T₂ → Stack Answer T₂

data State (Answer : Type) : Set where
    ⊢_↓_ : Stack Answer T → ⊨ T → State Answer
    ⊢_↑_ : Stack Answer T → ⊢ T → State Answer

private variable
    Answer : Type
    stack : Stack Answer T

data _⇾_ : State Answer → State Answer → Set where
  step-`    : ∀ {v : ⊨ T} {stack : Stack Answer T} → ⊢ stack ↑ ` v ⇾ ⊢ stack ↓ v
  step-⊞₁   : ⊢ stack ↑ (e₁ ⊞ e₂) ⇾ ⊢ stack ∷ (◌ ⊞₀ e₂) ↑ e₁
  step-⊞₂   : (⊢ stack ∷ (◌ ⊞₀ e₂) ↓ v₁) ⇾ (⊢ stack ∷ (v₁ ⊞₁ ◌) ↑ e₂)
  step-⊞₃   : (⊢ stack ∷ (v₁ ⊞₁ ◌) ↓ v₂) ⇾ (⊢ stack ↓ (v₁ + v₂))
  step-test  : ⊢ stack ↑ test e ⇾ ⊢ stack ∷ test ◌ ↑ e
  step-test₁ : ⊢ stack ∷ test ◌ ↓ n ⇾ ⊢ stack ↓ test' n
  step-𝚒𝚏   : (⊢ stack ↑ (if e then e₁ else e₂)) ⇾ (⊢ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) ↑ e)
  step-𝚝𝚑𝚎𝚗  : (⊢ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) ↓ true)  ⇾ (⊢ stack ↑ e₁)
  step-𝚎𝚕𝚜𝚎  : (⊢ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) ↓ false) ⇾ (⊢ stack ↑ e₂)

data _⇾⃰_ : State Answer → State Answer → Set where
  base  : ∀ {s : State Answer} → s ⇾⃰ s
  step  : ∀ {s₀ s₁ s₂ : State Answer} → s₀ ⇾ s₁ → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₂

⇾⃰-reflexive : ∀ {s : State Answer} → s ⇾⃰ s
⇾⃰-reflexive = base

⇾⃰-transitive : ∀ {s₀ s₁ s₂ : State Answer} → s₀ ⇾⃰ s₁ → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₂
⇾⃰-transitive base q = q
⇾⃰-transitive (step p q) r = step p (⇾⃰-transitive q r)

complete : ∀ (e : ⊢ T) (v : ⊨ T) (stack : Stack Answer T)
    → e ⇓ v
    → (⊢ stack ↑ e) ⇾⃰ (⊢ stack ↓ v)
complete (` x) v stack (` .x) =
    step step-` base
complete (e₀ ⊞ e₁) v stack (p₀ ⊞ p₁) =
    step step-⊞₁
    (⇾⃰-transitive (complete e₀ _ (stack ∷ ◌ ⊞₀ e₁) p₀)
    (step step-⊞₂ (⇾⃰-transitive (complete e₁ _ (stack ∷ _ ⊞₁ ◌) p₁)
    (step step-⊞₃ base))))
complete (test e) _ stack (test p) =
    step step-test
    (⇾⃰-transitive (complete e _ (stack ∷ test ◌) p)
    (step step-test₁ base))
complete (if e then e₁ else e₂) v stack (if-then p p₁) =
    step step-𝚒𝚏
    (⇾⃰-transitive (complete e _ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) p)
    (step step-𝚝𝚑𝚎𝚗
    (complete e₁ v stack p₁)))
complete (if e then e₁ else e₂) v stack (if-else p p₂) =
    step step-𝚒𝚏
    (⇾⃰-transitive (complete e _ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) p)
    (step step-𝚎𝚕𝚜𝚎
    (complete e₂ v stack p₂)))

det : ∀ {s₀ s₁ s₂ : State Answer} → s₀ ⇾ s₁ → s₀ ⇾ s₂ → s₁ ≡ s₂
det step-`    step-`    = reflexive
det step-⊞₁   step-⊞₁   = reflexive
det step-⊞₂   step-⊞₂   = reflexive
det step-⊞₃   step-⊞₃   = reflexive
det step-test  step-test  = reflexive
det step-test₁ step-test₁ = reflexive
det step-𝚒𝚏   step-𝚒𝚏   = reflexive
det step-𝚝𝚑𝚎𝚗  step-𝚝𝚑𝚎𝚗  = reflexive
det step-𝚎𝚕𝚜𝚎  step-𝚎𝚕𝚜𝚎  = reflexive

-- ⊢ [] ↓ v is a final state: no transition rule applies to it.
stuck : ∀ {T : Type} {v : ⊨ T} {s : State T} → (⊢ [] ↓ v) ⇾ s → ⊥
stuck ()

-- Two ⇾⃰-traces from the same start, each reaching a stuck state, reach the same state.
-- This follows directly from single-step determinism.
confluence : ∀ {s s₁ s₂ : State Answer}
    → s ⇾⃰ s₁ → s ⇾⃰ s₂
    → ({s' : State Answer} → s₁ ⇾ s' → ⊥)
    → ({s' : State Answer} → s₂ ⇾ s' → ⊥)
    → s₁ ≡ s₂
confluence base           base           _   _   = reflexive
confluence base           (step r   _  ) ns₁ _   = ⊥-elim (ns₁ r)
confluence (step r   _  ) base           _   ns₂ = ⊥-elim (ns₂ r)
confluence (step r₁ tr₁) (step r₂ tr₂) ns₁ ns₂ rewrite det r₁ r₂ =
    confluence tr₁ tr₂ ns₁ ns₂

-- Injectivity of the final-state constructor at the empty stack.
↓-inj : ∀ {Answer : Type} {v₁ v₂ : ⊨ Answer}
    → _≡_ {A = State Answer} (⊢ [] ↓ v₁) (⊢ [] ↓ v₂) → v₁ ≡ v₂
↓-inj reflexive = reflexive

-- Correctness: a machine run ⊢ [] ↑ e ⇾⃰ ⊢ [] ↓ v implies e ⇓ v.
-- Proof: by totality (e evaluates to some v′), completeness produces a canonical run to v′;
-- confluence of the two runs at the stuck final state yields v′ ≡ v.
correct : ∀ (e : ⊢ T) (v : ⊨ T)
    → (⊢ [] ↑ e) ⇾⃰ (⊢ [] ↓ v)
    → e ⇓ v
correct e v tr =
    let (v' ﹐ p) = total e
        
        tr'       : ⊢ [] ↑ e ⇾⃰ (⊢ [] ↓ v')
        tr'       = complete e v' [] p
        
        eq        : (⊢ [] ↓ v') ≡ (⊢ [] ↓ v)
        eq        = confluence tr' tr stuck stuck
    in subst (e ⇓_) (↓-inj eq) p
\end{code}

\begin{code}
open import Arith.Denotational as D

-- Corollary: if the denotational semantics gives v, the machine runs to v.
denot-to-machine : ∀ {T : Type} (e : ⊢ T) {v : ⊨ T}
    → D.⟦ e ⟧ ≡ v
    → (⊢ [] ↑ e) ⇾⃰ (⊢ [] ↓ v)
denot-to-machine e eq = complete e _ [] (D.simulateᴿ e eq)
\end{code}