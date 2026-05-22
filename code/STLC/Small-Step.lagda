\begin{code}
module STLC.Small-Step where
open import STLC.Definitions public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
\end{code}

Small-step operational semantics for the STLC.
\begin{code}
open import STLC.Big-Step
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Data.Product using (Σ; ∃; _×_) renaming (_,_ to _ʻ_; proj₂ to snd)

private
  variable
    n : ℕ
    b : 𝔹
    e₀ : Γ ⊢ T

data Normal : Γ ⊢ T → Set where
  nat     : Normal {Γ = Γ} (Nat n)
  bool    : Normal {Γ = Γ} (Bool b)
  closure : Normal {Γ = Γ} {T = T₁ ⇒ T₂} (ƛ e₀)

infix  40 _↦_
infixr 60 _[_]

private variable
  e : Γ ⊢ T

ext : ∀ {Γ Δ} 
    → (∀ {T} → T ∈ Γ → T ∈ Δ)
    → (∀ {T₁ T₂} → T₁ ∈ (Γ , T₂) → T₁ ∈ (Δ , T₂))
ext ρ Z = Z
ext ρ (S x) = S (ρ x)

rename : ∀ {Γ Δ}
  → (∀ {T} → T ∈ Γ → T ∈ Δ)
    -----------------------
  → (∀ {T} → Γ ⊢ T → Δ ⊢ T)
rename ρ (Nat x) = Nat x
rename ρ (Bool x) = Bool x
rename ρ (Var x) = Var (ρ x)
rename ρ (ƛ e) = ƛ (rename (ext ρ) e)
rename ρ (e₀ · e₁) = rename ρ e₀ · rename ρ e₁
rename ρ (e₀ ⊞ e₁) = rename ρ e₀ ⊞ rename ρ e₁
rename ρ (if e then e₁ else e₂) = if rename ρ e then rename ρ e₁ else rename ρ e₂

exts : ∀ {Γ Δ}
  → (∀ {T} → T ∈ Γ → Δ ⊢ T)
    -----------------------
  → (∀ {T₁ T₂} → T₁ ∈ (Γ , T₂) → (Δ , T₂) ⊢ T₁)
exts σ Z = Var Z
exts σ (S x) = rename S_ (σ x)

subst-tm : ∀ {Γ Δ}
  → (∀ {A} → A ∈ Γ → Δ ⊢ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst-tm σ (Nat x) = Nat x
subst-tm σ (Bool x) = Bool x
subst-tm σ (Var x) = σ x
subst-tm σ (ƛ e) = ƛ (subst-tm (exts σ) e)
subst-tm σ (e₀ ⊞ e₁) = subst-tm σ e₀ ⊞ subst-tm σ e₁
subst-tm σ (x · x₁) = subst-tm σ x · subst-tm σ x₁
subst-tm σ (if x then x₁ else x₂) = if subst-tm σ x then subst-tm σ x₁ else subst-tm σ x₂

_[_] : ∀ {Γ A B}
    → (Γ , B) ⊢ A
    → (Γ ⊢ B)
    → Γ ⊢ A
_[_] {Γ} {A} {B} e₁ e₂ = subst-tm σ e₁
    where
        σ : ∀ {A} → A ∈ (Γ , B) → Γ ⊢ A
        σ Z = e₂
        σ (S x) = Var x

data _↦_ : {Γ : Context} {T : Type} → (Γ ⊢ T) → (Γ ⊢ T) → Set where
  β-⊞ : ∀ {Γ} {n₁ n₂ : ℕ}
    -----------------------
    → (Nat {Γ = Γ} n₁ ⊞ Nat n₂) ↦ Nat (n₁ + n₂)

  β-if-true  : ∀{e₁ e₂ : Γ ⊢ T}
      → (if (Bool true) then e₁ else e₂) ↦ e₁

  β-if-false : ∀{e₁ e₂ : Γ ⊢ T}
      → (if (Bool false) then e₁ else e₂) ↦ e₂

  β-app : ∀ {e : (Γ , T₁) ⊢ T₂} {v : Γ ⊢ T₁}
      -----------------------
      → (ƛ e · v) ↦ e [ v ]

  ξ-app-left : ∀{e₁ e₁′ : Γ ⊢ (T₁ ⇒ T₂)} {e₂ : Γ ⊢ T₁}
      → e₁ ↦ e₁′
      → (e₁ · e₂) ↦ (e₁′ · e₂)

  ξ-app-right : ∀{e₁ : Γ ⊢ (T₁ ⇒ T₂)} {e₂ e₂′ : Γ ⊢ T₁}
      → Normal e₁
      → e₂ ↦ e₂′
      ----------------------------------
      → (e₁ · e₂) ↦ (e₁ · e₂′)

  ξ-⊞₁ : ∀{e₁ e₁′ : Γ ⊢ Nat} {e₂ : Γ ⊢ Nat}
      → e₁ ↦ e₁′
      ----------------------------------
      → (e₁ ⊞ e₂) ↦ (e₁′ ⊞ e₂)

  ξ-⊞₂ : ∀ {Γ} {n : ℕ} {e₂ e₂′ : Γ ⊢ Nat}
      → e₂ ↦ e₂′
      ----------------------------------
      → (Nat n ⊞ e₂) ↦ (Nat n ⊞ e₂′)

  ξ-if : ∀{e e′ : Γ ⊢ Bool} {e₁ e₂ : Γ ⊢ T}
      → e ↦ e′
      → (if e then e₁ else e₂) ↦ (if e′ then e₁ else e₂)

data _↦*_ : {Γ : Context} {T : Type} → (Γ ⊢ T) → (Γ ⊢ T) → Set where
  refl : ∀{e : Γ ⊢ T} → e ↦* e
  step : ∀{e₁ e₂ e₃ : Γ ⊢ T} → e₁ ↦ e₂ → e₂ ↦* e₃ → e₁ ↦* e₃

↦*-transitive : ∀{e₁ e₂ e₃ : Γ ⊢ T} → e₁ ↦* e₂ → e₂ ↦* e₃ → e₁ ↦* e₃
↦*-transitive refl q = q
↦*-transitive (step p r) q = step p (↦*-transitive r q)

private variable
  δ : Environment Γ
  v v′ : ⊨ T
  e′ : Γ ⊢ T

lift-⊞₁ : ∀ (e₂ : ∅ ⊢ Nat) {e₁ e₁′ : ∅ ⊢ Nat}
  → e₁ ↦* e₁′ → (e₁ ⊞ e₂) ↦* (e₁′ ⊞ e₂)
lift-⊞₁ e₂ refl        = refl
lift-⊞₁ e₂ (step r rs) = step (ξ-⊞₁ r) (lift-⊞₁ e₂ rs)

lift-⊞₂ : ∀ (n : ℕ) {e₂ e₂′ : ∅ ⊢ Nat}
  → e₂ ↦* e₂′ → (Nat n ⊞ e₂) ↦* (Nat n ⊞ e₂′)
lift-⊞₂ n refl        = refl
lift-⊞₂ n (step r rs) = step (ξ-⊞₂ r) (lift-⊞₂ n rs)

lift-if : ∀ (e₁ e₂ : ∅ ⊢ T) {e e′ : ∅ ⊢ Bool}
  → e ↦* e′ → (if e then e₁ else e₂) ↦* (if e′ then e₁ else e₂)
lift-if e₁ e₂ refl        = refl
lift-if e₁ e₂ (step r rs) = step (ξ-if r) (lift-if e₁ e₂ rs)

lift-·₁ : ∀ (e₂ : ∅ ⊢ T₁) {e₁ e₁′ : ∅ ⊢ (T₁ ⇒ T₂)}
  → e₁ ↦* e₁′ → (e₁ · e₂) ↦* (e₁′ · e₂)
lift-·₁ e₂ refl        = refl
lift-·₁ e₂ (step r rs) = step (ξ-app-left r) (lift-·₁ e₂ rs)

lift-·₂ : ∀ (e₁ : ∅ ⊢ (T₁ ⇒ T₂)) {e₂ e₂′ : ∅ ⊢ T₁}
  → Normal e₁ → e₂ ↦* e₂′ → (e₁ · e₂) ↦* (e₁ · e₂′)
lift-·₂ e₁ nf refl        = refl
lift-·₂ e₁ nf (step r rs) = step (ξ-app-right nf r) (lift-·₂ e₁ nf rs)
\end{code}

\begin{code}

embed : ∀ {T : Type} → ⊨ T → ∅ ⊢ T
embed {T = Bool} v = Bool v
embed {T = Nat} v = Nat v
embed {T = T₁ ⇒ T₂} ⟨ δᶜ , eᶜ ⟩ = ƛ {!   !}

-- Embed : {T : Type} → ⊨ T → Set
-- Embed {T = Bool} v = ∀ {Γ : Context} → Γ ⊢ Bool
-- Embed {T = Nat} v = ∀ {Γ : Context} → Γ ⊢ Nat
-- Embed {T = T₁ ⇒ T₂} (⟨_,_⟩ {Γᶜ} δᶜ eᶜ) = Γᶜ ⊢ (T₁ ⇒ T₂)

-- embed' :  ∀ {T : Type} → (v : ⊨ T) → Embed v
-- embed' {T = Bool} v = Bool v
-- embed' {T = Nat} v = Nat v
-- embed' {T = T₁ ⇒ T₂} ⟨ δᶜ , eᶜ ⟩ = ƛ eᶜ

-- sims : ∀ {Γ} {δ : Environment Γ} {e : ∅ ⊢ T} {v : ⊨ T}
--     → ∅ ⊢ e ⇓ v
--     → e ↦* embed' v
-- sims = ?


simulate : ∀ {Γ} {δ : Environment Γ} {e : ∅ ⊢ T} {v : ⊨ T}
    → ∅ ⊢ e ⇓ v
    → e ↦* embed v
simulate (NAT _) = refl
simulate (BOOL _) = refl
simulate (ABS e) = {!   !}
simulate (_⊞_ {e₁ = e₁} {v₁} {e₂} {v₂} p p₁) =
  ↦*-transitive (lift-⊞₁ {! embed v  !} (simulate p))
  (↦*-transitive (lift-⊞₂ {!   !} (simulate p₁))
  (step β-⊞ refl))

simulate (if-true p p₁) = {!   !}
simulate (if-false p p₁) = {!   !}
simulate (app p p₁ p₂) = {!   !}
\end{code}

\begin{code}
embed-bs : ∀ {T : Type} (v : ⊨ T) → ∅ ⊢ embed v ⇓ v
embed-bs {T = Bool} v = BOOL v
embed-bs {T = Nat} v = NAT v
embed-bs {T = T₁ ⇒ T₂} ⟨ δᶜ , eᶜ ⟩ = {!   !}


simulateᴿ : ∀ {e : ∅ ⊢ T} {v : ⊨ T} → e ↦* embed v → ∅ ⊢ e ⇓ v
simulateᴿ {v = v} refl = embed-bs v
simulateᴿ (step β-⊞ v) = {!   !}
simulateᴿ (step β-if-true v) = {!   !}
simulateᴿ (step β-if-false v) = {!   !}
simulateᴿ (step β-app v) = {!   !}
simulateᴿ (step (ξ-app-left x) v) = {!   !}
simulateᴿ (step (ξ-app-right x x₁) v) = {!   !}
simulateᴿ (step (ξ-⊞₁ x) v) = {!   !}
simulateᴿ (step (ξ-⊞₂ x) v) = {!   !}
simulateᴿ (step (ξ-if x) v) = {!   !}
\end{code}
