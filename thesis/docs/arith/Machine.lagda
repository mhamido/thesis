\begin{code}
module Arith.Machine where

open import Arith.Definitions public
open import Arith.Big-Step public

open import Data.Nat
open import Data.Bool hiding (T; if_then_else_) renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality.Core using (_≡_) renaming (refl to reflexive)
open import Data.Product using (∃) renaming (_,_ to _﹐_)


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
  step-` : ∀ {v : ⊨ T} {stack : Stack Answer T} → ⊢ stack ↑ ` v ⇾ ⊢ stack ↓ v
  step-⊞₁ : ⊢ stack ↑ (e₁ ⊞ e₂) ⇾ ⊢ stack ∷ (◌ ⊞₀ e₂) ↑ e₁
  step-⊞₂ : (⊢ stack ∷ (◌ ⊞₀ e₂) ↓ v₁) ⇾ (⊢ stack ∷ (v₁ ⊞₁ ◌) ↑ e₂) 
  step-⊞₃ : (⊢ stack ∷ (v₁ ⊞₁ ◌) ↓ v₂) ⇾ (⊢ stack ↓ (v₁ + v₂)) 
  step-𝚒𝚏 : (⊢ stack ↑ (if e then e₁ else e₂)) ⇾ (⊢ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) ↑ e) 
  step-𝚝𝚑𝚎𝚗 : (⊢ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) ↓ true) ⇾ ( ⊢ stack ↑ e₁)
  step-𝚎𝚕𝚜𝚎 : (⊢ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) ↓ false) ⇾ ( ⊢ stack ↑ e₂) 

data _⇾⃰_ : State Answer → State Answer → Set where
  base  : ∀ {s : State Answer}        → s ⇾⃰ s
  step  : ∀ {s₀ : State Answer} 
            {s₁ : State Answer} 
            {s₂ : State Answer} 
          → s₀ ⇾ s₁ → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₂


⇾⃰-reflexive : ∀ {s : State Answer} → s ⇾⃰ s
⇾⃰-reflexive = base

⇾⃰-transitive : ∀ {s₀ s₁ s₂ : State Answer} → s₀ ⇾⃰ s₁ → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₂
⇾⃰-transitive base q = q
⇾⃰-transitive (step p q) r = step p (⇾⃰-transitive q r)

complete' : ∀ (e : ⊢ T) (v : ⊨ T) (stack : Stack Answer T)
    → (⊢ stack ↑ e) ⇾⃰ (⊢ stack ↓ v)
    → e ⇓ v
complete' = {!   !}

complete : ∀ (e : ⊢ T) (v : ⊨ T)
    → (⊢ [] ↑ e) ⇾⃰ (⊢ [] ↓ v)
    → e ⇓ v
complete e v (step step-` base) = ` v
complete e v (step step-⊞₁ tr) = {!   !}
complete e v (step step-𝚒𝚏 tr) = {!   !}



correct : ∀ (e : ⊢ T) (v : ⊨ T) (stack : Stack Answer T)
    → e ⇓ v
    → (⊢ stack ↑ e) ⇾⃰ (⊢ stack ↓ v)
correct (` x) v stack (` .x) = step step-` base
correct (e₀ ⊞ e₁) v stack (p₀ ⊞ p₁) = 
    step step-⊞₁ 
    (⇾⃰-transitive (correct e₀ _ (stack ∷ ◌ ⊞₀ e₁) p₀) 
    (step step-⊞₂ (⇾⃰-transitive (correct e₁ _ (stack ∷ _ ⊞₁ ◌) p₁) 
    (step step-⊞₃ base))))

correct (test e) v stack (test p) = {!   !}
correct (if e then e₁ else e₂) v stack (if-then p p₁) = {!   !}
correct (if e then e₁ else e₂) v stack (if-else p p₁) = {!   !}


\end{code}