Mini2, a minuscule subset of F# featuring exceptions.

%------------------------------------------------------------------------------

\begin{code}
-- {-# OPTIONS --safe --without-K #-}

module Mini2 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality.Core using (_≡_) renaming (refl to reflexive)
open import Data.Nat renaming (_+_ to infixl 46 _+_; suc to succ)
open import Data.Product using (∃; _,_)
--open import VFP.List
\end{code}

\begin{code}
infix  149 `_
infixl 146 _⊞_
infix  120 𝚒𝚏_𝚝𝚑𝚎𝚗_𝚎𝚕𝚜𝚎_ try_catch_
infix  110 ⊢_

infixl 146 _⊞₀_ _⊞₁_
infix  120 _𝚎𝚕𝚜𝚎_ _catch_
infixr  35 _∷_
infix   30 _↓_ _↑_ _☇
\end{code}

%------------------------------------------------------------------------------

Representing types.

<<types>>
\begin{code}
data Type : Set where
  𝙱𝚘𝚘𝚕      : Type
  𝙽𝚊𝚝       : Type
  Exception : Type
\end{code}

\begin{code}
data Error : Set where
  error : Error
\end{code}

Interpreting an expression type as an Agda type. The value of e : ⊢ A
is an element of ⊨ A.

\begin{code}
⊨ : Type → Set
⊨ 𝙱𝚘𝚘𝚕     = 𝔹
⊨ 𝙽𝚊𝚝      = ℕ
⊨ Exception = Error
\end{code}

\begin{code}
private
  variable
    A B Answer : Type
\end{code}

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

\begin{code}
data Hole : Set where
  ◌ : Hole
\end{code}

%------------------------------------------------------------------------------

Static semantics (Church-style).

<<expressions>>
\begin{code}
data ⊢_ : Type → Set where
  `_            : ⊨ A → ⊢ A
  𝚒𝚏_𝚝𝚑𝚎𝚗_𝚎𝚕𝚜𝚎_  : ⊢ 𝙱𝚘𝚘𝚕 → ⊢ A → ⊢ A → ⊢ A
  _⊞_           : ⊢ 𝙽𝚊𝚝 → ⊢ 𝙽𝚊𝚝 → ⊢ 𝙽𝚊𝚝
  𝚝𝚎𝚜𝚝          : ⊢ 𝙽𝚊𝚝 → ⊢ 𝙱𝚘𝚘𝚕
  throw         : ⊢ A
  try_catch_    : ⊢ A → ⊢ A → ⊢ A

data _⇓_ : {A : Type} → ⊢ A → ⊨ A → Set where
  `_ : {v : ⊨ A} → ` v ⇓ v

  _⊞_ 
    : ∀ {e₁ e₂ : ⊢ 𝙽𝚊𝚝} {v₁ v₂}
    → e₁ ⇓ v₁
    → e₂ ⇓ v₂
    ----------------------------
    → (e₁ ⊞ e₂) ⇓ (v₁ + v₂)
  
  𝚝𝚎𝚜𝚝-0
    : ∀ {e : ⊢ 𝙽𝚊𝚝}
    → e ⇓ 0
    ----------------------------
    → (𝚝𝚎𝚜𝚝 e) ⇓ true

  𝚝𝚎𝚜𝚝-S
    : ∀ {e : ⊢ 𝙽𝚊𝚝} {n : ℕ}
    → e ⇓ succ n
    ----------------------------
    → (𝚝𝚎𝚜𝚝 e) ⇓ false

  𝚒𝚏-𝚝𝚑𝚎𝚗 
    : ∀ {e₁ : ⊢ 𝙱𝚘𝚘𝚕} {e₂ : ⊢ A} {v₂}
    → (p₀ : e₁ ⇓ true)
    → (p₁ : e₂ ⇓ v₂)
    → (e₃ : ⊢ A)
    ----------------------------
    → (𝚒𝚏 e₁ 𝚝𝚑𝚎𝚗 e₂ 𝚎𝚕𝚜𝚎 e₃) ⇓ v₂

  𝚒𝚏-𝚎𝚕𝚜𝚎
    : ∀ {e₁ : ⊢ 𝙱𝚘𝚘𝚕} {e₃ : ⊢ A} {v₃}
    → (p₀ : e₁ ⇓ false)
    → (e₂ : ⊢ A)
    → (p₂ : e₃ ⇓ v₃)
    ----------------------------
    → (𝚒𝚏 e₁ 𝚝𝚑𝚎𝚗 e₂ 𝚎𝚕𝚜𝚎 e₃) ⇓ v₃

  throw-error
    : throw ⇓ error

  try-ok
    : ∀ {e₁ : ⊢ A} {v}
    → (p : e₁ ⇓ v)
    → (e₂ : ⊢ A)
    ----------------------------
    → (try e₁ catch e₂) ⇓ v

  try-catch
    : ∀ {e₁ : ⊢ A} {e₂ : ⊢ A} {v}
    → e₁ ⇓ error
    → e₂ ⇓ v
    ----------------------------
    → (try e₁ catch e₂) ⇓ v
\end{code}

The first constructor embeds values into terms.

\begin{code}
example : ⊢ 𝙽𝚊𝚝
example = try ` 4711 ⊞ throw catch ` 815
\end{code}

-------------------------------------------------------------------------------

A small-step machine.

\begin{code}
data Frame : Type → Type → Set where
  _𝚎𝚕𝚜𝚎_  : ⊢ A → ⊢ A → Frame A 𝙱𝚘𝚘𝚕
  _⊞₀_    : Hole → ⊢ 𝙽𝚊𝚝 → Frame 𝙽𝚊𝚝 𝙽𝚊𝚝
  _⊞₁_    : ⊨ 𝙽𝚊𝚝 → Hole → Frame 𝙽𝚊𝚝 𝙽𝚊𝚝
  𝚝𝚎𝚜𝚝    : Hole → Frame 𝙱𝚘𝚘𝚕 𝙽𝚊𝚝
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
●  _☇: exception mode (unravelling the stack, searching for a handler).

\begin{code}
data State (Answer : Type) : Set where
  _↑_ : Stack Answer A → ⊢ A → State Answer
  _↓_ : Stack Answer A → ⊨ A → State Answer
  _☇  : Stack Answer A → State Answer
\end{code}

\begin{code}
private
  variable
    stack : Stack Answer A
\end{code}

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

\begin{code}
test : ℕ → 𝔹
test (zero)   = true
test (succ n) = false
\end{code}

\begin{code}
step : State Answer → State Answer
step (stack ↑ ` v)                   = stack ↓ v
step (stack ↑ 𝚒𝚏 e₀ 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) = stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↑ e₀
step (stack ↑ e₀ ⊞ e₁)               = stack ∷ (◌ ⊞₀ e₁) ↑ e₀
step (stack ↑ 𝚝𝚎𝚜𝚝 e)                = stack ∷ 𝚝𝚎𝚜𝚝 ◌ ↑ e
step (stack ↑ throw)                 = stack ☇
step (stack ↑ try e₁ catch e₂)       = stack ∷ ◌ catch e₂ ↑ e₁

step ([] ↓ v) = [] ↓ v

step (stack ∷ (e₁ 𝚎𝚕𝚜𝚎 e₂) ↓ v) = stack ↑ (if v then e₁ else e₂)
step (stack ∷ (◌ ⊞₀ e₁)    ↓ v) = stack ∷ (v ⊞₁ ◌) ↑ e₁
step (stack ∷ (n₀ ⊞₁ ◌)    ↓ v) = stack ↓ n₀ + v
step (stack ∷ 𝚝𝚎𝚜𝚝 ◌       ↓ v) = stack ↓ test v
step (stack ∷ ◌ catch e    ↓ v) = stack ↓ v

step ([] ☇) = [] ☇

step (stack ∷ e₁ 𝚎𝚕𝚜𝚎 e₂ ☇) = stack ☇
step (stack ∷ ◌ ⊞₀ e₁    ☇) = stack ☇
step (stack ∷ n₀ ⊞₁ ◌    ☇) = stack ☇
step (stack ∷ 𝚝𝚎𝚜𝚝 ◌     ☇) = stack ☇
step (stack ∷ ◌ catch e  ☇) = stack ↑ e
\end{code}

\begin{code}
steps : ℕ → State Answer → State Answer
steps (zero)   s = s
steps (succ n) s = step (steps n s)

go = steps 8 ([] ↑ example)

deterministic : ∀ {T : Type} {e : ⊢ T} {v₁ v₂ : ⊨ T } → e ⇓ v₁ → e ⇓ v₂ → v₁ ≡ v₂
deterministic `_ `_ = reflexive
deterministic (p₁ ⊞ p₂) (q₁ ⊞ q₂) with deterministic p₁ q₁ | deterministic p₂ q₂
... | reflexive | reflexive = reflexive
deterministic (𝚒𝚏-𝚝𝚑𝚎𝚗 p₁ p₂ e₃) (𝚒𝚏-𝚝𝚑𝚎𝚗 q₁ q₂ e₄) = deterministic p₂ q₂
deterministic (𝚒𝚏-𝚎𝚕𝚜𝚎 p₁ e₂ p₃) (𝚒𝚏-𝚎𝚕𝚜𝚎 q₁ e₃ q₃) = deterministic p₃ q₃
deterministic (𝚒𝚏-𝚝𝚑𝚎𝚗 p₁ p₂ e₃) (𝚒𝚏-𝚎𝚕𝚜𝚎 q₁ e₂ q₃) with deterministic p₁ q₁ 
... | ()
deterministic (𝚒𝚏-𝚎𝚕𝚜𝚎 p₁ e₂ p₃) (𝚒𝚏-𝚝𝚑𝚎𝚗 q₁ q₂ e₃) with deterministic p₁ q₁ 
... | ()
deterministic throw-error throw-error = reflexive
deterministic (try-ok p e₂) (try-ok q e₃) = deterministic p q
deterministic (try-ok p e₂) (try-catch q₁ q₂) with deterministic p q₁
... | ()
deterministic (try-catch p₁ p₂) (try-ok q e₂) with deterministic q p₁
... | ()
deterministic (try-catch p₁ p₂) (try-catch q₁ q₂) = deterministic p₂ q₂
deterministic (𝚝𝚎𝚜𝚝-0 p) (𝚝𝚎𝚜𝚝-0 q) = reflexive
deterministic (𝚝𝚎𝚜𝚝-0 p) (𝚝𝚎𝚜𝚝-S q) with deterministic p q
... | ()
deterministic (𝚝𝚎𝚜𝚝-S p) (𝚝𝚎𝚜𝚝-0 q) with deterministic p q
... | ()
deterministic (𝚝𝚎𝚜𝚝-S p) (𝚝𝚎𝚜𝚝-S q) = reflexive

postulate
  total : ∀ {T : Type} (e : ⊢ T) → ∃ (λ v → e ⇓ v)
-- total (` x) = x , `_
-- total (𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) with total e | total e₁ | total e₂
-- ... | false , p₁ | v₂ , p₂ | v₃ , p₃ = v₃ , (𝚒𝚏-𝚎𝚕𝚜𝚎 p₁ e₁ p₃)
-- ... | true  , p₁ | v₂ , p₂ | v₃ , p₃ = v₂ , (𝚒𝚏-𝚝𝚑𝚎𝚗 p₁ p₂ e₂)
-- ... | error , p₁ | v₂ , p₂ | v₃ , p₃ = error , (𝚒𝚏-𝚝𝚑𝚎𝚗 p₁ p₂ e₂)
-- total (e₁ ⊞ e₂) with total e₁ | total e₂
-- ... | v₁ , p₁ | v₂ , p₂ = v₁ + v₂ , (p₁ ⊞ p₂)
-- total (𝚝𝚎𝚜𝚝 e) with total e
-- ... | zero , p = true , 𝚝𝚎𝚜𝚝-0 p
-- ... | succ v , p = false , 𝚝𝚎𝚜𝚝-S p
-- total (throw {Exception}) = error , throw-error
-- total (throw {𝙱𝚘𝚘𝚕}) = true , throw-error
-- total (throw {𝙽𝚊𝚝}) = zero , throw-error
-- total (try e catch e₁) with total e | total e₁
-- ... | error , p | v₁ , p₁ = v₁ , try-catch p p₁
-- ... | v , p | v₁ , p₁ = v , try-ok p e₁
\end{code}


