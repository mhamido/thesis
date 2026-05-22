\begin{code}
module STLC.Machine where

open import STLC.Definitions public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import STLC.Big-Step public
open import Relation.Nullary using (¬_)
open import Data.Product using (∃) renaming (_,_ to _﹐_; proj₁ to fst; proj₂ to snd)
open import Data.Empty using (⊥; ⊥-elim)

infix 5 _⇾_ _⇾⃰_
infix 70 _⊞₀_ _⊞₁_ _𝚎𝚕𝚜𝚎_

private variable
  A B : Type

data Hole : Set where
  ◌ : Hole

data Frame : Type → Type → Set where
  _𝚎𝚕𝚜𝚎_  : Γ ⊢ A → Γ ⊢ A → Frame A Bool
  _⊞₀_    : Hole → Γ ⊢ Nat → Frame Nat Nat
  _⊞₁_    : ⊨ Nat → Hole → Frame Nat Nat
  
  app₁    : Hole 
          → Γ ⊢ A
          → Frame B (A ⇒ B)

  app₂    : ⊨ (A ⇒ B)
          → Hole 
          → Frame B A

  app₃    : Environment Γ 
          → ⊨ (A ⇒ B)
          → ⊨ A 
          → Hole
          → Frame B B

data Stack (Answer : Type) : Type → Set where
  []  : Stack Answer Answer
  _∷_ : Stack Answer A → Frame A B → Stack Answer B
infixr 60 _∷_

data State (Answer : Type) : Set where
  _⊢_↑_ : (δ : Environment Γ) → Stack Answer A → Γ ⊢ A → State Answer
  _⊢_↓_ : (δ : Environment Γ) → Stack Answer A →   ⊨ A → State Answer

infix 10 _⊢_↑_

private variable
  Answer : Type
  stack : Stack Answer A
  δ δ′ : Environment Γ
  Δ : Context
  δᶜ : Environment Δ
  eᶜ : (Δ , T₁) ⊢ T₂
  e e₁ e₂ : Γ ⊢ T
  v v₁ v₂ v₃ : ⊨ T
  x : T ∈ Γ

data _⇾_ : State Answer → State Answer → Set where
  step-Nat : ∀ {n : ℕ} {stack : Stack Answer Nat} → (δ ⊢ stack ↑ Nat n) ⇾ (δ ⊢ stack ↓ n)
  step-Bool : ∀ {b : 𝔹} {stack : Stack Answer Bool} → (δ ⊢ stack ↑ Bool b) ⇾ (δ ⊢ stack ↓ b)
  step-⊞₁ : (δ ⊢ stack ↑ e₁ ⊞ e₂) ⇾ (δ ⊢ stack ∷ (◌ ⊞₀ e₂) ↑ e₁) 
  step-⊞₂ : (δ ⊢ stack ∷ (◌ ⊞₀ e₂) ↓ v₁) ⇾ (δ ⊢ stack ∷ (v₁ ⊞₁ ◌) ↑ e₂) 
  step-⊞₃ : (δ ⊢ stack ∷ (v₁ ⊞₁ ◌) ↓ v₂) ⇾ (δ ⊢ stack ↓ (v₁ + v₂)) 
  step-𝚒𝚏 : (δ ⊢ stack ↑ if e then e₁ else e₂) ⇾ (δ ⊢ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) ↑ e) 
  step-𝚝𝚑𝚎𝚗 : (δ ⊢ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) ↓ true) ⇾ (δ ⊢ stack ↑ e₁)
  step-𝚎𝚕𝚜𝚎 : (δ ⊢ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) ↓ false) ⇾ (δ ⊢ stack ↑ e₂) 
  step-var : (δ ⊢ stack ↑ Var x) ⇾ (δ ⊢ stack ↓ lookupₑ δ x) 
  step-· : (δ ⊢ stack ↑ (e₁ · e₂)) ⇾ (δ ⊢ stack ∷ app₁ ◌ e₂ ↑ e₁) 
  step-ƛ : (δ ⊢ stack ↑ (ƛ e)) ⇾ (δ ⊢ stack ↓ ⟨ δ , e ⟩) 
  step-·₁ : (δ ⊢ stack ∷ app₁ ◌ e₂ ↓ v₁) ⇾ (δ ⊢ stack ∷ app₂ v₁ ◌ ↑ e₂)
  step-·₂ : ∀ {v₂ : ⊨ A}
          → (δ ⊢ stack ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌ ↓ v₂) ⇾ ((δᶜ , v₂) ⊢ (stack ∷ app₃ δ ⟨ δᶜ , eᶜ ⟩ v₂ ◌) ↑ eᶜ) 
  step-·₃ : ∀ {stack : Stack Answer B} {v₁ : ⊨ (A ⇒ B)} {v₂ : ⊨ A}
          → (δ ⊢ stack ∷ app₃ δ′ ⟨ δᶜ , eᶜ ⟩ v₂ ◌ ↓ v₃) ⇾ (δ′ ⊢ stack ↓ v₃) 

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

infix  0 proof_
infixr 1 ⇾-link ⇾⃰-link
infix  2 _∎

proof_ : {s₁ s₂ : State  Answer} → s₁ ⇾⃰ s₂ → s₁ ⇾⃰ s₂
proof s₁⇾⃰s₂ = s₁⇾⃰s₂

syntax ⇾-link x q p = x ⇾⟨ p ⟩ q
⇾-link : (s₀ : State Answer) {s₁ s₂ : State Answer} → s₁ ⇾⃰ s₂ → s₀ ⇾ s₁ → s₀ ⇾⃰ s₂
⇾-link _ q p = step p q

syntax ⇾⃰-link x q p = x ⇾⃰⟨ p ⟩ q
⇾⃰-link : (s₀ : State Answer) {s₁ s₂ : State Answer} → s₁ ⇾⃰ s₂ → s₀ ⇾⃰ s₁ → s₀ ⇾⃰ s₂
⇾⃰-link _ q p = ⇾⃰-transitive p q

_∎ : (s : State Answer) → s ⇾⃰ s
e ∎ = ⇾⃰-reflexive

data Final : State Answer → Set where
  final : ∀ {δ : Environment Γ} {v : ⊨ A} → Final (δ ⊢ [] ↓ v)

-- Single-step determinism.
det : ∀ {s₀ s₁ s₂ : State Answer} → s₀ ⇾ s₁ → s₀ ⇾ s₂ → s₁ ≡ s₂
det step-Nat    step-Nat    = refl
det step-Bool   step-Bool   = refl
det step-⊞₁    step-⊞₁    = refl
det step-⊞₂    step-⊞₂    = refl
det step-⊞₃    step-⊞₃    = refl
det step-𝚒𝚏    step-𝚒𝚏    = refl
det step-𝚝𝚑𝚎𝚗   step-𝚝𝚑𝚎𝚗   = refl
det step-𝚎𝚕𝚜𝚎   step-𝚎𝚕𝚜𝚎   = refl
det step-var   step-var   = refl
det step-·     step-·     = refl
det step-ƛ     step-ƛ     = refl
det step-·₁    step-·₁    = refl
det step-·₂    step-·₂    = refl
det step-·₃    step-·₃    = refl

-- ⊢ [] ↓ v is a final state: no transition rule applies.
stuck : ∀ {Γ} {δ : Environment Γ} {A} {v : ⊨ A} {s : State A} → (δ ⊢ [] ↓ v) ⇾ s → ⊥
stuck ()

-- Confluence: two ⇾⃰ traces from the same start each ending in a stuck state reach the same state.
confluence : ∀ {s s₁ s₂ : State Answer}
    → s ⇾⃰ s₁ → s ⇾⃰ s₂
    → ({s' : State Answer} → s₁ ⇾ s' → ⊥)
    → ({s' : State Answer} → s₂ ⇾ s' → ⊥)
    → s₁ ≡ s₂
confluence base           base           _   _   = refl
confluence base           (step r   _  ) ns₁ _   = ⊥-elim (ns₁ r)
confluence (step r   _  ) base           _   ns₂ = ⊥-elim (ns₂ r)
confluence (step r₁ tr₁) (step r₂ tr₂) ns₁ ns₂ rewrite det r₁ r₂ =
    confluence tr₁ tr₂ ns₁ ns₂

-- Injectivity of the final-state constructor.
↓-inj : ∀ {Γ} {δ : Environment Γ} {A} {v₁ v₂ : ⊨ A}
    → _≡_ {A = State A} (δ ⊢ [] ↓ v₁) (δ ⊢ [] ↓ v₂) → v₁ ≡ v₂
↓-inj refl = refl

complete 
  : ∀ (δ : Environment Γ) (stack : Stack Answer T) (e : Γ ⊢ T) (v : ⊨ T) (p : δ ⊢ e ⇓ v)
  → (δ ⊢ stack ↑ e ⇾⃰  δ ⊢ stack ↓ v)
complete δ stack (Nat _) v (NAT _) = step step-Nat base
complete δ stack (Bool _) v (BOOL _) = step step-Bool base
complete δ stack (Var _) v (VAR _) = step step-var base
complete δ stack (ƛ _) v (ABS _) = step step-ƛ base
complete δ stack (e₁ ⊞ e₂) v (_⊞_ {v₁ = v₁} {v₂ = v₂} p₁ p₂) =
  proof
    δ ⊢ stack ↑ e₁ ⊞ e₂
  ⇾⟨ step-⊞₁ ⟩
    δ ⊢ stack ∷ (◌ ⊞₀ e₂) ↑ e₁
  ⇾⃰⟨ complete δ (stack ∷ (◌ ⊞₀ e₂)) e₁ v₁ p₁ ⟩
    δ ⊢ stack ∷ (◌ ⊞₀ e₂) ↓ v₁
  ⇾⟨ step-⊞₂ ⟩
    δ ⊢ stack ∷ (v₁ ⊞₁ ◌) ↑ e₂
  ⇾⃰⟨ complete δ (stack ∷ (v₁ ⊞₁ ◌)) e₂ v₂ p₂ ⟩
    δ ⊢ stack ∷ (v₁ ⊞₁ ◌) ↓ v₂
  ⇾⟨ step-⊞₃ ⟩
    δ ⊢ stack ↓ (v₁ + v₂)
  ∎

complete δ stack (if e then e₁ else e₂) v (if-true p₀ p₁) = 
  proof
    δ ⊢ stack ↑ if e then e₁ else e₂
  ⇾⟨ step-𝚒𝚏 ⟩
    δ ⊢ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) ↑ e
  ⇾⃰⟨ complete δ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) e true p₀ ⟩
    δ ⊢ stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↓ true
  ⇾⟨ step-𝚝𝚑𝚎𝚗 ⟩
    δ ⊢ stack ↑ e₁
  ⇾⃰⟨ complete δ stack e₁ v p₁ ⟩
    δ ⊢ stack ↓ v
  ∎

complete δ stack (if e then e₁ else e₂) v (if-false p₀ p₁) =
  proof
    δ ⊢ stack ↑ if e then e₁ else e₂
  ⇾⟨ step-𝚒𝚏 ⟩
    δ ⊢ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) ↑ e
  ⇾⃰⟨ complete δ (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂)) e false p₀ ⟩
    δ ⊢ stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↓ false
  ⇾⟨ step-𝚎𝚕𝚜𝚎 ⟩
    δ ⊢ stack ↑ e₂
  ⇾⃰⟨ complete δ stack e₂ v p₁ ⟩
    δ ⊢ stack ↓ v
  ∎

complete δ stack (e₀ · e₁) v (app {δᶜ = δᶜ} {eᶜ} {v₁} p p₁ p₂) =
  proof
    δ ⊢ stack ↑ (e₀ · e₁)
  ⇾⟨ step-· ⟩
    δ ⊢ stack ∷ app₁ ◌ e₁ ↑ e₀
  ⇾⃰⟨ complete δ (stack ∷ app₁ ◌ e₁) e₀ ⟨ δᶜ , eᶜ ⟩ p ⟩
    δ ⊢ stack ∷ app₁ ◌ e₁ ↓ ⟨ δᶜ , eᶜ ⟩
  ⇾⟨ step-·₁ ⟩
    δ ⊢ stack ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌ ↑ e₁
  ⇾⃰⟨ complete δ (stack ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌) e₁ v₁ p₁ ⟩
    δ ⊢ stack ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌ ↓ v₁
  ⇾⟨ step-·₂ ⟩
    (δᶜ , v₁) ⊢ stack ∷ app₃ δ ⟨ δᶜ , eᶜ ⟩ v₁ ◌ ↑ eᶜ
  ⇾⃰⟨ complete (δᶜ , v₁) (stack ∷ app₃ δ ⟨ δᶜ , eᶜ ⟩ v₁ ◌) eᶜ v p₂ ⟩
    (δᶜ , v₁) ⊢ stack ∷ app₃ δ ⟨ δᶜ , eᶜ ⟩ v₁ ◌ ↓ v
  ⇾⟨ step-·₃ {v₁ = ⟨ δᶜ , eᶜ ⟩} ⟩
    δ ⊢ stack ↓ v
  ∎

correct : ∀ {Γ} (δ : Environment Γ) (e : Γ ⊢ T) (v : ⊨ T)
    → (δ ⊢ [] ↑ e) ⇾⃰ (δ ⊢ [] ↓ v)
    → δ ⊢ e ⇓ v
correct δ e v tr =
    let (v' ﹐ p) = total e
        tr'       : (δ ⊢ [] ↑ e) ⇾⃰ (δ ⊢ [] ↓ v')
        tr'       = complete δ [] e v' p
        eq        : (δ ⊢ [] ↓ v') ≡ (δ ⊢ [] ↓ v)
        eq        = confluence tr' tr stuck stuck
    in subst (δ ⊢ e ⇓_) (↓-inj eq) p
\end{code}