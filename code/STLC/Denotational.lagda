\begin{code}
module STLC.Denotational where

open import STLC.Definitions public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
\end{code}

Denotational semantics for the STLC.

\begin{code}
⟪_⟫ : Type → Set
⟪ Bool  ⟫ = 𝔹
⟪ Nat   ⟫ = ℕ
⟪ T₁ ⇒ T₂ ⟫ = ⟪ T₁ ⟫ → ⟪ T₂ ⟫

open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_) renaming (_,_ to _⸴_)

-- Environment for denotational semantics
Env : Context → Set
Env ∅ = ⊤
Env (Γ , T) = Env Γ × ⟪ T ⟫

lookupᵈ : ∀{Γ T} → Env Γ → T ∈ Γ → ⟪ T ⟫
lookupᵈ (Γ ⸴ x) Z = x
lookupᵈ (Γ ⸴ x) (S n) = lookupᵈ Γ n

interpret : ∀{Γ T} → Env Γ → (Γ ⊢ T) → ⟪ T ⟫
interpret δ (Nat x) = x
interpret δ (Bool x) = x
interpret δ (e₁ ⊞ e₂) = interpret δ e₁ + interpret δ e₂
interpret δ (Var x) = lookupᵈ δ x
interpret δ (ƛ e) = λ z → interpret (δ ⸴ z) e
interpret δ (e₁ · e₂) = (interpret δ e₁) (interpret δ e₂)
interpret δ (if e then e₁ else e₂) with interpret δ e
... | true = interpret δ e₁
... | false = interpret δ e₂

\end{code}


The closure-based denotational semantics reuses the value type from the big-step
semantics so that the two can be directly related.
\begin{code}
open import STLC.Big-Step public

{-# TERMINATING #-}
apply : {T₁ T₂ : Type} → Closure T₁ T₂ → ⊨ T₁ → ⊨ T₂

evaluate : {Γ : Context} → Environment Γ → (Γ ⊢ T) → ⊨ T
evaluate δ (Nat v)                  = v
evaluate δ (Bool v)                 = v
evaluate δ (Var x)                  = lookupₑ δ x
evaluate δ (ƛ e)                    = ⟨ δ , e ⟩
evaluate δ (e₁ ⊞ e₂)                = evaluate δ e₁ + evaluate δ e₂
evaluate δ (e₁ · e₂) with evaluate δ e₁
... | ⟨ δᶜ , eᶜ ⟩                   = apply ⟨ δᶜ , eᶜ ⟩ (evaluate δ e₂)
evaluate δ (if e₀ then e₁ else e₂) with evaluate δ e₀
... | true                          = evaluate δ e₁
... | false                         = evaluate δ e₂

apply ⟨ δᶜ , eᶜ ⟩ v = evaluate (δᶜ , v) eᶜ
\end{code}

\begin{code}
open import Data.Product using (∃) renaming (_,_ to _ʻ_)

{-# TERMINATING #-}
simulate : ∀ {Γ} {δ : Environment Γ} (e : Γ ⊢ T) {v : ⊨ T}
    → evaluate δ e ≡ v
    → δ ⊢ e ⇓ v
simulate (Nat x) refl = NAT x
simulate (Bool x) refl = BOOL x
simulate (ƛ e) refl = ABS e
simulate (e₁ ⊞ e₂) refl = simulate e₁ refl ⊞ simulate e₂ refl
simulate (Var x) refl = VAR x
simulate {δ = δ} (e₁ · e₂) refl with evaluate δ e₁ in eq 
... | ⟨ δᶜ , eᶜ ⟩ = app (simulate e₁ eq) (simulate e₂ refl) (simulate eᶜ refl)  
simulate {δ = δ} (if e₀ then e₁ else e₂) refl with evaluate δ e₀ in eq
... | true = if-true (simulate e₀ eq) (simulate e₁ refl)
... | false = if-false (simulate e₀ eq) (simulate e₂ refl)


simulateᴿ : ∀ {Γ} {δ : Environment Γ} {e : Γ ⊢ T} {v : ⊨ T}
    → δ ⊢ e ⇓ v
    → evaluate δ e ≡ v
simulateᴿ (NAT _)            = refl
simulateᴿ (BOOL _)           = refl
simulateᴿ (VAR _)            = refl
simulateᴿ (ABS _)            = refl
simulateᴿ (p₁ ⊞ p₂)          rewrite simulateᴿ p₁ | simulateᴿ p₂ = refl
simulateᴿ (if-true  pe p₁)   rewrite simulateᴿ pe = simulateᴿ p₁
simulateᴿ (if-false pe p₂)   rewrite simulateᴿ pe = simulateᴿ p₂
simulateᴿ (app p₁ p₂ p₃)     rewrite simulateᴿ p₁ | simulateᴿ p₂ = simulateᴿ p₃

\end{code}

Closure denotational is equivalent to the direct denotational semantics.
The logical relation connects values of `⊨ T` (w. closures) with
values of `⟪ T ⟫` (w. functions).  
\begin{code}
relates : (A : Type) → ⊨ A → ⟪ A ⟫ → Set
syntax relates A a₁ a₂ = a₁ ~⟨ A ⟩~ a₂

x₁ ~⟨ Nat  ⟩~ x₂ = x₁ ≡ x₂
x₁ ~⟨ Bool ⟩~ x₂ = x₁ ≡ x₂
f₁ ~⟨ T₁ ⇒ T₂ ⟩~ f₂ = ∀ {a₁ a₂}
    → a₁ ~⟨ T₁ ⟩~ a₂
    → apply f₁ a₁ ~⟨ T₂ ⟩~ f₂ a₂

open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_) renaming (_,_ to _⸴_)


EnvRel : ∀ {Γ} → Environment Γ → Env Γ → Set
EnvRel {∅}     ∅       tt      = ⊤
EnvRel {_ , T} (δ , v) (δ' ⸴ w) = EnvRel δ δ' × v ~⟨ T ⟩~ w

lookup-rel : ∀ {Γ T} {δ : Environment Γ} {δ' : Env Γ}
    → EnvRel δ δ' → (x : T ∈ Γ)
    → lookupₑ δ x ~⟨ T ⟩~ lookupᵈ δ' x
lookup-rel {δ = _ , _} {δ' = _ ⸴ _} (_ ⸴ r)  Z     = r
lookup-rel {δ = _ , _} {δ' = _ ⸴ _} (rs ⸴ _) (S x) = lookup-rel rs x

{-# TERMINATING #-}
correct : ∀ {Γ} {δ : Environment Γ} {δ' : Env Γ} (e : Γ ⊢ T)
    → EnvRel δ δ'
    → evaluate δ e ~⟨ T ⟩~ interpret δ' e
correct (Nat _)  _  = refl
correct (Bool _) _  = refl
correct (Var x)  rs = lookup-rel rs x
correct (ƛ e)    rs = λ ra → correct e (rs ⸴ ra)
correct (e₁ ⊞ e₂) rs rewrite correct e₁ rs | correct e₂ rs = refl
correct (if e then e₁ else e₂) rs
    with evaluate _ e
... | true  with interpret _ e
...   | true  = correct e₁ rs
...   | false with correct e rs
...     | ()
... | false with interpret _ e
...   | true  with correct e rs
...     | ()
...   | false = correct e₂ rs
correct (e₁ · e₂) rs = correct e₁ rs (correct e₂ rs)

\end{code}