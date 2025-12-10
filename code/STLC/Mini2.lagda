Mini2, a minuscule subset of F# featuring exceptions.

%------------------------------------------------------------------------------

\begin{code}
-- {-# OPTIONS --safe --without-K #-}
module STLC.Mini2 where

open import Data.Empty using (⊥) renaming (⊥-elim to ex-falso)
open import Data.Bool renaming (Bool to 𝔹) hiding (T)
open import Relation.Binary.PropositionalEquality.Core using (_≡_) renaming (refl to reflexive)
open import Data.Nat renaming (_+_ to infixl 46 _+_; suc to succ)
open import Data.Product using (∃) renaming (_,_ to _﹐_)
open import Data.Sum using (_⊎_) renaming (inj₁ to ok; inj₂ to err)
\end{code}

\begin{code}
infix  149 `_
infixl 146 _⊞_
infix  120 𝚒𝚏_𝚝𝚑𝚎𝚗_𝚎𝚕𝚜𝚎_
infix  110 _⊢_
infixr  20 _⇒_

infixl 146 _⊞₀_ _⊞₁_
infix  120 _𝚎𝚕𝚜𝚎_
infixr  35 _∷_
infix   30 _⊢_↓_ _⊢_↑_
\end{code}

%------------------------------------------------------------------------------

Representing types.

<<types>>
\begin{code}
data Type : Set where
  𝙱𝚘𝚘𝚕 : Type
  𝙽𝚊𝚝  : Type
  _⇒_  : Type → Type → Type

test : ℕ → 𝔹
test zero = true
test (succ n) = false
\end{code}

Interpreting an expression type as an Agda type. The value of e : ⊢ A
is an element of ⊨ A.

\begin{code}
open import Context Type public

mutual
  ⊨ : Type → Set
  ⊨ 𝙱𝚘𝚘𝚕     = 𝔹
  ⊨ 𝙽𝚊𝚝      = ℕ
  ⊨ (a ⇒ b)  = Closure a b

  record Closure (T₁ T₂ : Type) : Set where
    inductive 
    constructor closure
    field
      {Γᶜ} : Context
      δᶜ : Environment Γᶜ
      eᶜ : (Γᶜ , T₁) ⊢ T₂

  open import Environment Type ⊨ public
\end{code}

\begin{code}
  private
    variable
      A B T T₁ T₂ Answer : Type
      Γ : Context
      δ : Environment Γ
\end{code}

%------------------------------------------------------------------------------

Static semantics (Church-style).

<<expressions>>
\begin{code}
  data _⊢_ : Context → Type → Set where
    `_            : ⊨ A → Γ ⊢ A
    𝚒𝚏_𝚝𝚑𝚎𝚗_𝚎𝚕𝚜𝚎_ : Γ ⊢ 𝙱𝚘𝚘𝚕 → Γ ⊢ A   → Γ ⊢ A → Γ ⊢ A
    _⊞_           : Γ ⊢ 𝙽𝚊𝚝  → Γ ⊢ 𝙽𝚊𝚝 → Γ ⊢ 𝙽𝚊𝚝
    𝚝𝚎𝚜𝚝          : Γ ⊢ 𝙽𝚊𝚝  → Γ ⊢ 𝙱𝚘𝚘𝚕
    Var           : A ∈ Γ    → Γ ⊢ A
    _·_           : Γ ⊢ (A ⇒ B) → Γ ⊢ A → Γ ⊢ B
    ƛ_            : (Γ , A) ⊢ B → Γ ⊢ (A ⇒ B)
    -- Let_In_       : Γ ⊢ A → (Γ , A) ⊢ B → Γ ⊢ B
    -- LetRec_       : (Γ , T₁ ⇒ T₂ , T₁) ⊢ T₂ → Γ ⊢ (T₁ ⇒ T₂)
  infixl 10 _·_

private variable
  e e₁ e₂ e₃ : Γ ⊢ T
  v v₁ v₂ v₃ : ⊨ T
  n n₁ n₂ : ⊨ 𝙽𝚊𝚝

data _⊢_⇓_ : Environment Γ → Γ ⊢ A → ⊨ A → Set where
  `_ : (v : ⊨ A) → δ ⊢ ` v ⇓ v

  _⊞_ 
    : δ ⊢ e₁ ⇓ v₁
    → δ ⊢ e₂ ⇓ v₂
    ----------------------------
    → δ ⊢ (e₁ ⊞ e₂) ⇓ (v₁ + v₂)

  𝚝𝚎𝚜𝚝
    : ∀ {e : Γ ⊢ 𝙽𝚊𝚝} {n : ℕ}
    → δ ⊢ e ⇓ n
    ----------------------------
    → δ ⊢ (𝚝𝚎𝚜𝚝 e) ⇓ (test n)

  𝚒𝚏-𝚝𝚑𝚎𝚗 
    : (p₀ : δ ⊢ e₁ ⇓ true)
    → (p₁ : δ ⊢ e₂ ⇓ v₂)
    → (e₃ : Γ ⊢ A)
    ----------------------------
    → δ ⊢ (𝚒𝚏 e₁ 𝚝𝚑𝚎𝚗 e₂ 𝚎𝚕𝚜𝚎 e₃) ⇓ v₂

  𝚒𝚏-𝚎𝚕𝚜𝚎
    : (p₀ : δ ⊢ e₁ ⇓ false)
    → (e₂ : Γ ⊢ A)
    → (p₂ : δ ⊢ e₃ ⇓ v₃)
    ----------------------------
    → δ ⊢ (𝚒𝚏 e₁ 𝚝𝚑𝚎𝚗 e₂ 𝚎𝚕𝚜𝚎 e₃) ⇓ v₃

  var 
    : ∀ (v : A ∈ Γ)
    ---------------------------
    → δ ⊢ (Var v) ⇓ lookupₑ δ v

  fun : (e₁ : (Γ , A) ⊢ B)
    -----------------
    → δ ⊢ (ƛ e₁) ⇓ closure δ e₁

  app 
    : ∀ {Γᶜ} {δᶜ : Environment Γᶜ} {eᶜ} {x : ⊨ A}
    → δ ⊢ e₁ ⇓ closure {T₂ = B} δᶜ eᶜ
    → δ ⊢ e₂ ⇓ x
    → (δᶜ , x) ⊢ eᶜ ⇓ v
    → δ ⊢ (e₁ · e₂) ⇓ v
\end{code}

The first constructor embeds values into terms.

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

\begin{code}
data Hole : Set where
  ◌ : Hole
\end{code}

-------------------------------------------------------------------------------

A small-step machine.

\begin{code}
data Frame : Type → Type → Set where
  _𝚎𝚕𝚜𝚎_  : Γ ⊢ A → Γ ⊢ A → Frame A 𝙱𝚘𝚘𝚕
  _⊞₀_    : Hole → Γ ⊢ 𝙽𝚊𝚝 → Frame 𝙽𝚊𝚝 𝙽𝚊𝚝
  _⊞₁_    : δ ⊢ e ⇓ n → Hole → Frame 𝙽𝚊𝚝 𝙽𝚊𝚝
  
  𝚝𝚎𝚜𝚝    : Hole → Frame 𝙱𝚘𝚘𝚕 𝙽𝚊𝚝
  app₁    : Hole → Γ ⊢ A → Frame B (A ⇒ B)
  app₂    : ∀ {e₁ : Γ ⊢ (A ⇒ B) } {v₁ : ⊨ (A ⇒ B)} 
          → δ ⊢ e₁ ⇓ v₁ → Hole → Frame B A
  app₃    : ∀ {e₁ :  Γ ⊢ (A ⇒ B) } {e₂ : Γ ⊢ A} {v₁ : ⊨ (A ⇒ B)} {v₂ : ⊨ A}
          → δ ⊢ e₁ ⇓ v₁ → δ ⊢ e₂ ⇓ v₂ → Hole → Frame B B

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
% ●  _☇: exception mode (unravelling the stack, searching for a handler).

\begin{code} -- todo: change this to include context & env like how its done in milli
data State (Answer : Type) : Set where
  -- _⊢_↑_ : (δ : Environment Γ) → Stack Answer A → Γ ⊢ A → State Answer
  -- _⊢_↓_ : (δ : Environment Γ) → Stack Answer A → {e : Γ ⊢ A} {v : ⊨ A} → δ ⊢ e ⇓ v → State Answer
  _⊢_↓_ : {Γ : Context} → (δ : Environment Γ) 
        → Stack Answer T 
        → {e : Γ ⊢ T} 
        → δ ⊢ e ⇓ v → State Answer

  _⊢_↑_ : (δ : Environment Γ) 
        → Stack Answer T 
        → Γ ⊢ T 
        → State Answer
\end{code}

\begin{code}
private
  variable
    stack : Stack Answer A
\end{code}

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

\begin{code}
postulate 
  step : State Answer → State Answer
-- step (δ ⊢ stack ↑ ` v)                    = δ ⊢ stack ↓ (` v)
-- step (δ ⊢ stack ↑ (𝚒𝚏 v 𝚝𝚑𝚎𝚗 v₁ 𝚎𝚕𝚜𝚎 v₂)) = δ ⊢ stack ∷ v₁ 𝚎𝚕𝚜𝚎 v₂ ↑ v
-- step (δ ⊢ stack ↑ (e₁ ⊞ e₂))              = δ ⊢ stack ∷ ◌ ⊞₀ e₂ ↑ e₁
-- step (δ ⊢ stack ↑ 𝚝𝚎𝚜𝚝 e)                 = δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e
-- step (δ ⊢ stack ↑ Var x)                  = δ ⊢ stack ↓ var x
-- step (δ ⊢ stack ↑ (e₁ · e₂))              = δ ⊢ stack ∷ app₁ ◌ e₂ ↑ e₁
-- step (δ ⊢ stack ↑ (ƛ e))                  = δ ⊢ stack ↓ fun e

-- step (δ ⊢ [] ↓ v) = δ ⊢ [] ↓ v
-- step (δ ⊢ stack ∷ x 𝚎𝚕𝚜𝚎 x₁ ↓ v) = δ ⊢ stack ∷ x 𝚎𝚕𝚜𝚎 x₁ ↓ v
-- step (δ ⊢ stack ∷ ◌ ⊞₀ x₁ ↓ v) = {! δ ⊢ stack ↓ v !}
-- step (δ ⊢ stack ∷ x ⊞₁ x₁ ↓ v) = {!   !}
-- step (δ ⊢ stack ∷ 𝚝𝚎𝚜𝚝 x ↓ v) = δ ⊢ stack ↓ 𝚝𝚎𝚜𝚝 v
-- step (δ ⊢ stack ∷ app₁ x x₁ ↓ v) = {!   !}
-- step (δ ⊢ stack ∷ app₂ x x₁ ↓ v) = {!   !}
-- step (δ ⊢ stack ∷ app₃ x x₁ x₂ ↓ v) = {!   !}
-- step (δ ⊢ stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ↓ v) = {!   !}
-- step (δ ⊢ stack ∷ ◌ ⊞₀ e₁ ↓ v) = δ ⊢ stack ∷ {!   !} ↑ {! e₁  !}

-- step (stack ↑ ` v)                   = stack ↓ v
-- step (stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) = stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↑ e₀
-- step (stack ↑ e₀ ⊞ e₁)               = stack ∷ (◌ ⊞₀ e₁) ↑ e₀
-- step (stack ↑ 𝚝𝚎𝚜𝚝 e)                = stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e
-- step (stack ↑ Var n)                 = stack ↓ {!   !} -- need someway to return `n`!
-- step (stack ↑ (f · x))               = stack ∷ App₁ ◌ x ↑ f
-- step (stack ↑ (ƛ e))                 = stack ↓ closure {!   !} e

-- step ([] ↓ v) = [] ↓ v

-- step (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↓ v) = stack ↑ (if v then e₁ else e₂)
-- step (stack ∷ (◌ ⊞₀ e₁)    ↓ v) = stack ∷ (v ⊞₁ ◌) ↑ e₁
-- step (stack ∷ (n₀ ⊞₁ ◌)    ↓ v) = stack ↓ n₀ + v
-- step (stack ∷ 𝚝𝚎𝚜𝚝 ◌       ↓ v) = stack ↓ test v

-- step (stack ∷ App₁ ◌ x ↓ f) = stack ∷ App₂ {! f !} ◌ ↑ x
-- step (stack ∷ App₂ f ◌ ↓ x) = stack ∷ App₃ {!   !} {! x  !} ◌ ↑ {! f  !}
-- step (stack ∷ App₃ f x ◌ ↓ v) = {! stack  !}
\end{code}

\begin{code}
steps : ℕ → State Answer → State Answer
steps (zero)   s = s
steps (succ n) s = step (steps n s)

deterministic : ∀ {T : Type} {e : Γ ⊢ T} {v₁ v₂ : ⊨ T} → δ ⊢ e ⇓ v₁ → δ ⊢ e ⇓ v₂ → v₁ ≡ v₂
deterministic (` _) (` _) = reflexive
deterministic (p₁ ⊞ p₂) (q₁ ⊞ q₂) with deterministic p₁ q₁ | deterministic p₂ q₂
... | reflexive | reflexive = reflexive
deterministic (𝚒𝚏-𝚝𝚑𝚎𝚗 p₁ p₂ e₃) (𝚒𝚏-𝚝𝚑𝚎𝚗 q₁ q₂ e₄) = deterministic p₂ q₂
deterministic (𝚒𝚏-𝚎𝚕𝚜𝚎 p₁ e₂ p₃) (𝚒𝚏-𝚎𝚕𝚜𝚎 q₁ e₃ q₃) = deterministic p₃ q₃
deterministic (𝚒𝚏-𝚝𝚑𝚎𝚗 p₁ p₂ e₃) (𝚒𝚏-𝚎𝚕𝚜𝚎 q₁ e₂ q₃) with deterministic p₁ q₁ 
... | ()
deterministic (𝚒𝚏-𝚎𝚕𝚜𝚎 p₁ e₂ p₃) (𝚒𝚏-𝚝𝚑𝚎𝚗 q₁ q₂ e₃) with deterministic p₁ q₁ 
... | ()
deterministic (𝚝𝚎𝚜𝚝 p) (𝚝𝚎𝚜𝚝 q) with deterministic p q
... | reflexive = reflexive

deterministic (var v) (var u) = reflexive
deterministic (fun e₁) (fun e₂) = reflexive
deterministic (app f₁ x₁ v₁) (app f₂ x₂ v₂) with deterministic f₁ f₂ | deterministic x₁ x₂
... | reflexive | reflexive = deterministic v₁ v₂

-- apply : Closure A B → ⊨ A → ⊨ B
-- apply (closure δᶜ eᶜ) x = {!   !}

total : ∀ {T : Type} (e : Γ ⊢ T) → ∃ (λ v → δ ⊢ e ⇓ v)
total (` x) = x ﹐ ` x 
total (𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) = {!   !} ﹐ {!   !} !}
tal (e ⊞ e₁) = {!   !}
total (𝚝𝚎𝚜𝚝 e) = {!   !}
total (Var x) = {!   !}
total (e · e₁) = {!   !}
total (ƛ e) = {!   !}

-- total (` x) = x ﹐ ` x

-- total (𝚝𝚎𝚜𝚝 e) with total e
-- ... | v ﹐ p = test v ﹐ 𝚝𝚎𝚜𝚝 p

-- total (𝚒𝚏 e₁ 𝚝𝚑𝚎𝚗 e₂ 𝚎𝚕𝚜𝚎 e₃) with total e₁ | total e₂ | total e₃
-- ... | false ﹐ p₁ | _ | v ﹐ p₂ = v ﹐ (𝚒𝚏-𝚎𝚕𝚜𝚎 p₁ e₂ p₂)
-- ... | true  ﹐ p₁ | v ﹐ p₂ | _ = v ﹐ (𝚒𝚏-𝚝𝚑𝚎𝚗 p₁ p₂ e₃)

-- total (e₁ ⊞ e₂) with total e₁ | total e₂
-- ... | v₁ ﹐ p₁ | v₂ ﹐ p₂ = v₁ + v₂ ﹐ p₁ ⊞ p₂

-- total {δ = δ} (Var x) = lookupₑ δ x ﹐ var x

-- total (ƛ e) = closure _ e ﹐ fun e
-- total (f · x) with total f | total x 
-- ... | closure δᶜ eᶜ ﹐ p₁ | x ﹐ p₂ = {!   !} ﹐ (app p₁ p₂ {!   !})


\end{code}


