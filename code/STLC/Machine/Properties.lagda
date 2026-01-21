\begin{code}
{-# OPTIONS --allow-unsolved-metas #-}
module STLC.Machine.Properties where

open import STLC.Machine.Definitions public
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_) renaming (refl to reflexive)
open import Data.Product using (∃) renaming (_,_ to _﹐_; proj₂ to snd)
open import Data.Empty using (⊥) renaming (⊥-elim to ex-falso-quodlibet)
open import Data.Bool hiding (_≟_)
open import Data.Nat using (_+_; zero; suc; ℕ)
\end{code}

\begin{code}
private variable
    Answer : Type
    Γ : Context
    δ : Environment Γ
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
deterministic step-` step-` = reflexive
deterministic step-⊞₁ step-⊞₁ = reflexive
deterministic step-⊞₂ step-⊞₂ = reflexive
deterministic step-⊞₃ step-⊞₃ = reflexive
deterministic step-𝚝𝚎𝚜𝚝₁ step-𝚝𝚎𝚜𝚝₁ = reflexive
deterministic step-𝚒𝚏 step-𝚒𝚏 = reflexive
deterministic step-𝚝𝚑𝚎𝚗 step-𝚝𝚑𝚎𝚗 = reflexive
deterministic step-𝚎𝚕𝚜𝚎 step-𝚎𝚕𝚜𝚎 = reflexive
deterministic step-· step-· = reflexive
deterministic step-ƛ step-ƛ = reflexive
deterministic step-𝚝𝚎𝚜𝚝₂ step-𝚝𝚎𝚜𝚝₂ = reflexive
deterministic step-·₁ step-·₁ = reflexive
deterministic step-·₂ step-·₂ = reflexive
deterministic step-·₃ step-·₃ = reflexive
deterministic step-Var step-Var = reflexive
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
  : ∀ {Γ Δ : Context} {T : Type}
  → (δ : Environment Δ) (stack : Stack Answer Γ Δ T) (e : Δ ⊢ T) 
  → ∀ (v : ⊨ T) (p : δ ⊢ e ⇓ v) 
  → (δ ⊢ stack ↑ e) ⇾⃰ (δ ⊢ stack ↓ v)
complete δ stack (` x) v (` .x) = step step-` base
complete δ stack (Var x) v (var v₁) = step step-Var base
complete δ stack (ƛ e) v (fun e₁) = step step-ƛ base
complete δ stack (e₁ ⊞ e₂) v (_⊞_ {v₁ = v₁} {v₂ = v₂} p₁ p₂) =
  proof
    δ ⊢ stack ↑ e₁ ⊞ e₂
  ⇾⟨ step-⊞₁ ⟩
    δ ⊢ stack ∷ ◌ ⊞₀ e₂ ↑ e₁
  ⇾⃰⟨ complete δ (stack ∷ ◌ ⊞₀ e₂) e₁ v₁ p₁ ⟩
    δ ⊢ stack ∷ ◌ ⊞₀ e₂ ↓ v₁
  ⇾⟨ step-⊞₂ ⟩
    δ ⊢ stack ∷ v₁ ⊞₁ ◌ ↑ e₂
  ⇾⃰⟨ complete δ (stack ∷ v₁ ⊞₁ ◌) e₂ v₂ p₂ ⟩
    δ ⊢ stack ∷ v₁ ⊞₁ ◌ ↓ v₂
  ⇾⟨ step-⊞₃ ⟩
    δ ⊢ stack ↓ v
  ∎

complete δ stack (𝚝𝚎𝚜𝚝 e) v (𝚝𝚎𝚜𝚝 {n = n} p) =
    proof
    δ ⊢ stack ↑ 𝚝𝚎𝚜𝚝 e
  ⇾⟨ step-𝚝𝚎𝚜𝚝₁ ⟩
    δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e
  ⇾⃰⟨ complete δ (stack ∷ 𝚝𝚎𝚜𝚝 ◌) e n p ⟩
    δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↓ n
  ⇾⟨ step-𝚝𝚎𝚜𝚝₂ ⟩
    δ ⊢ stack ↓ test n
  ∎

complete δ stack (𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) v (𝚒𝚏-𝚝𝚑𝚎𝚗 p p₁ e₃) =
  proof
    δ ⊢ stack ↑ 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂
  ⇾⟨ step-𝚒𝚏 ⟩
    δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↑ e
  ⇾⃰⟨ complete δ (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) e true p ⟩
    δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ true
  ⇾⟨ step-𝚝𝚑𝚎𝚗 ⟩
    δ ⊢ stack ↑ e₁
  ⇾⃰⟨ complete δ stack e₁ v p₁ ⟩
    δ ⊢ stack ↓ v
  ∎

complete δ stack (𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) v (𝚒𝚏-𝚎𝚕𝚜𝚎 p e₃ p₁) =
  proof
    δ ⊢ stack ↑ 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂
  ⇾⟨ step-𝚒𝚏 ⟩
    δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↑ e
  ⇾⃰⟨ complete δ (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) e false p ⟩
    δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ false
  ⇾⟨ step-𝚎𝚕𝚜𝚎 ⟩
    δ ⊢ stack ↑ e₂
  ⇾⃰⟨ complete δ stack e₂ v p₁ ⟩
    δ ⊢ stack ↓ v
  ∎

complete δ stack (e₁ · e₂) v (app {δᶜ = δᶜ} {eᶜ = eᶜ} {v₁ = v₁} p p₁ p₂) = 
  proof
    δ ⊢ stack ↑ (e₁ · e₂)
  ⇾⟨ step-· ⟩ 
    δ ⊢ stack ∷ app₁ ◌ e₂ ↑ e₁
  ⇾⃰⟨ complete δ (stack ∷ app₁ ◌ e₂) e₁ ⟨ δᶜ , eᶜ ⟩ p ⟩
    δ ⊢ stack ∷ app₁ ◌ e₂ ↓ ⟨ δᶜ , eᶜ ⟩
  ⇾⟨ step-·₁ ⟩
    δ ⊢ stack ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌ ↑ e₂
  ⇾⃰⟨ complete δ (stack ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌) e₂ v₁ p₁ ⟩
    δ ⊢ stack ∷ app₂ ⟨ δᶜ , eᶜ ⟩ ◌ ↓ v₁
  ⇾⟨ step-·₂ ⟩
    (δᶜ , v₁) ⊢ stack ∷ app₃ δ ⟨ δᶜ , eᶜ ⟩ v₁ ◌ ↑ eᶜ
  ⇾⃰⟨ complete (δᶜ , v₁) (stack ∷ app₃ δ ⟨ δᶜ , eᶜ ⟩ v₁ ◌) eᶜ v p₂ ⟩
    (δᶜ , v₁) ⊢ stack ∷ app₃ δ ⟨ δᶜ , eᶜ ⟩ v₁ ◌ ↓ v
  ⇾⟨ step-·₃ { h₌ = reflexive } ⟩
    δ ⊢ stack ↓ v
  ∎

complete´ 
  : ∀ {A : Type}
  → (e : Γ ⊢ A) (v : ⊨ A)
  → (p : δ ⊢ e ⇓ v)
  → ∀ {s : Stack Answer Γ Γ A} 
  → (δ ⊢ s ↑ e) ⇾⃰ (δ ⊢ s ↓ v)
complete´ e v p = complete _ _ e v p

Total 
    : ∀ {A : Type} {stack : Stack Answer Γ Γ A}
    → (e : Γ ⊢ A) 
    → ∃ (λ v → (δ ⊢ stack ↑ e) ⇾⃰  (δ ⊢ stack ↓ v))
Total e with ↓-total e
... | x ﹐ p = x ﹐ complete _ _ e x p
\end{code}

-------------------------------------------------------------------------------

\begin{code}
expr : State Answer → ∃ (λ Γ → Γ ⊢ Answer)
expr (δ ⊢ s ↓ v) = _ ﹐ s [ ` v ]
expr (δ ⊢ s ↑ e) = _ ﹐ s [ e ]
\end{code}

-------------------------------------------------------------------------------

Correctness. The proof below mimics the proof that small-step implies big-step.

\begin{code}
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

infix 2 _⪅_
_⪅_ : {A : Type} → Γ ⊢ A → Γ ⊢ A → Set
e ⪅ e′  =  ∀ {δ} {v} → δ ⊢ e ⇓ v → δ ⊢ e′ ⇓ v  -- simulation / refinement

test-ctx
    : {e e′ : Γ ⊢ 𝙽𝚊𝚝}
    → e ⪅ e′ → 𝚝𝚎𝚜𝚝 e ⪅ 𝚝𝚎𝚜𝚝 e′
test-ctx r (𝚝𝚎𝚜𝚝 p) = 𝚝𝚎𝚜𝚝 (r p)

plus-ctx₁
    : {e e′ e₁ : Γ ⊢ 𝙽𝚊𝚝}
    → e ⪅ e′ → e ⊞ e₁ ⪅ e′ ⊞ e₁
plus-ctx₁ r (p₁ ⊞ p₂) = r p₁ ⊞ p₂

plus-ctx₂
    : {e e′ : Γ ⊢ 𝙽𝚊𝚝} {n₀ : ℕ}
    → e ⪅ e′ → ` n₀ ⊞ e ⪅ ` n₀ ⊞ e′
plus-ctx₂ r (p₁ ⊞ p₂) = p₁ ⊞ r p₂

if-ctx
    : {A : Type} {e e′ : Γ ⊢ 𝙱𝚘𝚘𝚕} {e₁ e₂ : Γ ⊢ A} 
    → e ⪅ e′ → 𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂ ⪅ 𝚒𝚏 e′ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂
if-ctx r (𝚒𝚏-𝚝𝚑𝚎𝚗 p₀ p₁ e₂) = 𝚒𝚏-𝚝𝚑𝚎𝚗 (r p₀) p₁ e₂
if-ctx r (𝚒𝚏-𝚎𝚕𝚜𝚎 p₀ e₁ p₂) = 𝚒𝚏-𝚎𝚕𝚜𝚎 (r p₀) e₁ p₂

app-ctx₁
    : {A B : Type} {e e′ : Γ ⊢ (A ⇒ B)} {e₂ : Γ ⊢ A} 
    → e ⪅ e′ → e · e₂ ⪅ e′ · e₂
app-ctx₁ r (app p p₁ p₂) = app (r p) p₁ p₂

app-ctx₂ 
    : {A B : Type} {f : ⊨ (A ⇒ B)} {e e′ : Γ ⊢ A}
    → e ⪅ e′ → ` f · e ⪅ ` f · e′
app-ctx₂ r (app (` _) p₁ p₂) = app (` _) (r p₁) p₂

⪅-refl : {A : Type} {e : Γ ⊢ A} → e ⪅ e
⪅-refl p = p

⪅-compositional 
    : ∀ {Γ Δ : Context} {A : Type} {e e′ : Δ ⊢ A} 
    → e ⪅ e′ 
    → ∀ (s : Stack Answer Γ Δ A) 
    → s [ e ] ⪅ s [ e′ ]
⪅-compositional r [] = r
⪅-compositional r (s ∷ e₁ 𝚎𝚕𝚜𝚎 e₂) = ⪅-compositional (if-ctx r) s
⪅-compositional r (s ∷ ◌  ⊞₀ e₁)   = ⪅-compositional (plus-ctx₁ r) s
⪅-compositional r (s ∷ n₀ ⊞₁  ◌)   = ⪅-compositional (plus-ctx₂ r) s
⪅-compositional r (s ∷    𝚝𝚎𝚜𝚝 ◌)  = ⪅-compositional (test-ctx r) s
⪅-compositional r (s ∷ app₁ ◌ e₂)  = ⪅-compositional (app-ctx₁ r) s
⪅-compositional r (s ∷ app₂ f ◌)   = ⪅-compositional (app-ctx₂ r) s
⪅-compositional r (s ∷ app₃ δ f x ◌) = ⪅-compositional ⪅-refl s
\end{code}

...............................................................................

\begin{code}
plus-refine : ∀ {n₀ n₁ : ℕ} → ` (n₀ + n₁) ⪅ ` n₀ ⊞ ` n₁
plus-refine (` _) = ` _ ⊞ ` _

test-refine : ∀ {n : ℕ} → ` test n ⪅ 𝚝𝚎𝚜𝚝 (` n)
test-refine (` _) = 𝚝𝚎𝚜𝚝 (` _)

if-then-refine 
    : ∀ {A : Type} {e₁ e₂ : Γ ⊢ A} 
    → e₁ ⪅ 𝚒𝚏 ` true 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂
if-then-refine p = 𝚒𝚏-𝚝𝚑𝚎𝚗 (` true)  p _

if-else-refine
    : ∀ {A : Type} {e₁ e₂ : Γ ⊢ A} 
    → e₂ ⪅ 𝚒𝚏 ` false 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂
if-else-refine p = 𝚒𝚏-𝚎𝚕𝚜𝚎 (` false) _ p
\end{code}

The following refinement rules are slightly troublesome.

- Looking up a variable in the environment refines to a variable expression.
  var-refine: lookupₑ δ x ⪅ Var x

- a closure value refines to a lambda.
  lam-refine: ` ⟨ δ , e ⟩ ⪅ ƛ e

— the result of evaluating the closure body refines to the application of the closure to the argument
  app-refine: (δᶜ , v₁) ⊢ eᶜ ⇓ v → ` v ⪅ ` ⟨ δᶜ , eᶜ ⟩ · ` v₁

The issue was that ⪅ quantifies over all environments, but these rules specifically needs the environments between the two to match.
(See similar issue below.)

\begin{code}
var-refine 
    : {A : Type} {δ : Environment Γ} {x : A ∈ Γ}
    → δ ⊢ ` lookupₑ δ x ⇓ lookupₑ δ x 
    → δ ⊢ Var x ⇓ lookupₑ δ x
var-refine (` _) = var _

lam-refine 
    : ∀ {A B : Type} {δ : Environment Γ} {e : (Γ Context., A) ⊢ B}
    → δ ⊢ ` ⟨ δ , e ⟩ ⇓ ⟨ δ , e ⟩
    → δ ⊢ ƛ e ⇓ ⟨ δ , e ⟩
lam-refine (` ⟨ δ , e ⟩) = fun e

app-refine 
    : ∀ {A B : Type} {δᶜ : Environment Γ} {eᶜ : (Γ Context., A) ⊢ B} {v₁ : ⊨ A} {v : ⊨ B}
    → (δᶜ Environment., v₁) ⊢ eᶜ ⇓ v
    → ` v ⪅ ` ⟨ δᶜ , eᶜ ⟩ · ` v₁
app-refine p (` _) = app (` _) (` _) p
\end{code}

\begin{code}
private variable
    A : Type
\end{code}

\begin{code}
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)

_≡₁_ : (t₁ t₂ : Type) → Dec (t₁ ≡ t₂)
𝙱𝚘𝚘𝚕 ≡₁ 𝙱𝚘𝚘𝚕 = yes reflexive
𝙱𝚘𝚘𝚕 ≡₁ 𝙽𝚊𝚝 = no λ ()
𝙱𝚘𝚘𝚕 ≡₁ (t₂ ⇒ t₃) = no λ ()
𝙽𝚊𝚝 ≡₁ 𝙱𝚘𝚘𝚕 = no λ ()
𝙽𝚊𝚝 ≡₁ 𝙽𝚊𝚝 = yes reflexive
𝙽𝚊𝚝 ≡₁ (t₂ ⇒ t₃) = no λ ()
(t₁ ⇒ t₂) ≡₁ 𝙱𝚘𝚘𝚕 = no λ ()
(t₁ ⇒ t₂) ≡₁ 𝙽𝚊𝚝 = no λ ()
(t₁ ⇒ t₂) ≡₁ (t₃ ⇒ t₄) with t₁ ≡₁ t₃ | t₂ ≡₁ t₄ 
... | no p | no q = no λ where reflexive → p reflexive
... | no p | yes q = no λ where reflexive → p reflexive
... | yes p | no q = no λ where reflexive → q reflexive
... | yes reflexive | yes reflexive = yes reflexive 

_≟ᶜ_ : (Δ Γ : Context) → Dec (Δ ≡ Γ)
∅ ≟ᶜ ∅ = yes reflexive
∅ ≟ᶜ (Γ Context., x) = no λ ()
(Δ Context., x) ≟ᶜ ∅ = no λ () 
(Δ Context., t₁) ≟ᶜ (Γ Context., t₂) with Δ ≟ᶜ Γ | t₁ ≡₁ t₂
... | no p  | no  q = no λ where reflexive → p reflexive
... | no p  | yes q = no λ where reflexive → p reflexive
... | yes p | no  q = no λ where reflexive → q reflexive
... | yes reflexive | yes reflexive = yes reflexive

-- The refinement relation holds when the expressions are evaluated within the same context (and environment).
-- This is necessary because of the return type of `expr`.


_⪅₂_ : {A : Type} → ∃ (λ Γ → Γ ⊢ A) → ∃ (λ Γ → Γ ⊢ A) → Set
(Γ ﹐ e₁) ⪅₂ (Δ ﹐ e₂) with Γ ≟ᶜ Δ
... | no  _ = ⊤
... | yes reflexive = e₁ ⪅ e₂

-- TODO: Does the refines-to relation actually preserve the environment?
-- s -> s' doesn't necessarily have the same context, notably the case where `app3` is on the stack.

postulate 
    step-sim : ∀ {s s′ : State Answer} → s ⇾ s′ →  (expr s′) ⪅₂ (expr s)

simulateᴿ : ∀ {s s′ : State Answer} → s ⇾⃰ s′ → (expr s′) ⪅₂ (expr s)
simulateᴿ base = {!   !}
simulateᴿ (step x thing) = {!   !}
-- simulateᴿ base q = q
-- simulateᴿ (step p ps) q = step-sim p (simulateᴿ ps q)

correct : ∀ {e : ∅ ⊢ A} {v : ⊨ A} → (∅ ⊢ [] ↑ e ⇾⃰ ∅ ⊢ [] ↓ v) → ∅ ⊢ e ⇓ v
correct p = simulateᴿ p (` _)
\end{code}
