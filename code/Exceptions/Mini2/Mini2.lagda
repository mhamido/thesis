Mini2, a minuscule subset of F# featuring exceptions.

%------------------------------------------------------------------------------

\begin{code}
-- {-# OPTIONS --safe --without-K #-}
{-# OPTIONS --without-K #-}
module Mini2 where

open import Data.Empty using (⊥) renaming (⊥-elim to ex-falso)
open import Data.Bool renaming (Bool to 𝔹)
open import Relation.Binary.PropositionalEquality.Core using (_≡_) renaming (refl to reflexive)
open import Data.Nat renaming (_+_ to infixl 46 _+_; suc to succ)
open import Data.Product using (∃; _,_)
open import Data.Sum using (_⊎_) renaming (inj₁ to ok; inj₂ to err)
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

test : ℕ → 𝔹
test zero = true
test (succ n) = false
\end{code}

Interpreting an expression type as an Agda type. The value of e : ⊢ A
is an element of ⊨ A.

\begin{code}
⊨ : Type → Set
⊨ 𝙱𝚘𝚘𝚕     = 𝔹
⊨ 𝙽𝚊𝚝      = ℕ
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

-- A * (B + C) = A * B + A * C. 
-- where A = |- T, B = |= T, and C = Exn

mutual
 data _⇑ : {A : Type} → ⊢ A → Set where
   throw-error
     : ∀ {A} → throw {A = A}  ⇑

   _⊞₁_ 
     : ∀ {e₁ e₂ : ⊢ 𝙽𝚊𝚝}
     → e₁ ⇑
     ----------------------------
     → (e₁ ⊞ e₂) ⇑

   _⊞₂_ 
     : ∀ {e₁ e₂ : ⊢ 𝙽𝚊𝚝} {v₁}
     → e₁ ⇓ v₁
     → e₂ ⇑
     ----------------------------
     → (e₁ ⊞ e₂) ⇑


   𝚝𝚎𝚜𝚝-error
     : ∀ {e : ⊢ 𝙽𝚊𝚝}
     → e ⇑
     ----------------------------
     → (𝚝𝚎𝚜𝚝 e) ⇑

   𝚒𝚏₁ : ∀ {e₁ : ⊢ 𝙱𝚘𝚘𝚕}
     → (p₀ : e₁ ⇑)
     → (e₂ : ⊢ A)
     → (e₃ : ⊢ A)
     ----------------------------
     → (𝚒𝚏 e₁ 𝚝𝚑𝚎𝚗 e₂ 𝚎𝚕𝚜𝚎 e₃) ⇑
     
   𝚒f₂ 
     : ∀ {e₁ : ⊢ 𝙱𝚘𝚘𝚕} {e₂ : ⊢ A}
     → (p₀ : e₁ ⇓ true)
     → (p₁ : e₂ ⇑)
     → (e₃ : ⊢ A)
     ----------------------------
     → (𝚒𝚏 e₁ 𝚝𝚑𝚎𝚗 e₂ 𝚎𝚕𝚜𝚎 e₃) ⇑

   𝚒𝚏₃
     : ∀ {e₁ : ⊢ 𝙱𝚘𝚘𝚕} {e₃ : ⊢ A}
     → (p₀ : e₁ ⇓ false)
     → (e₂ : ⊢ A)
     → (p₂ : e₃ ⇑)
     ----------------------------
     → (𝚒𝚏 e₁ 𝚝𝚑𝚎𝚗 e₂ 𝚎𝚕𝚜𝚎 e₃) ⇑


   try-rethrow
     : ∀ {e₁ e₂ : ⊢ A}
     → e₁ ⇑
     → e₂ ⇑ 
     ----------------------------
     → (try e₁ catch e₂) ⇑


 data _⇓_ : {A : Type} → ⊢ A → ⊨ A → Set where
   `_ : (v : ⊨ A) → ` v ⇓ v

   _⊞_ 
     : ∀ {e₁ e₂ : ⊢ 𝙽𝚊𝚝} {v₁ v₂}
     → e₁ ⇓ v₁
     → e₂ ⇓ v₂
     ----------------------------
     → (e₁ ⊞ e₂) ⇓ (v₁ + v₂)

   𝚝𝚎𝚜𝚝
     : ∀ {e : ⊢ 𝙽𝚊𝚝} {n : ℕ}
     → e ⇓ n
     ----------------------------
     → (𝚝𝚎𝚜𝚝 e) ⇓ (test n)

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

   try-ok
     : ∀ {e₁ : ⊢ A} {v}
     → (p : e₁ ⇓ v)
     → (e₂ : ⊢ A)
     ----------------------------
     → (try e₁ catch e₂) ⇓ v

   try-catch
     : ∀ {e₁ : ⊢ A} {e₂ : ⊢ A} {v}
     → e₁ ⇑
     → e₂ ⇓ v
     ----------------------------
     → (try e₁ catch e₂) ⇓ v

 _⇓ʳ_ : {A : Type} (e : ⊢ A) (v : ⊨ A) → Set
 e ⇓ʳ v =  (e ⇓ v) ⊎ (e ⇑)

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

mutual
  discriminate : ∀ {T : Type} {e : ⊢ T} {v : ⊨ T} → e ⇓ v → e ⇑ → ⊥
  discriminate (` _) ()
  discriminate (p ⊞ p₁) (_⊞₁_ q) = discriminate p q
  discriminate (p ⊞ p₁) (x ⊞₂ q) = discriminate p₁ q
  discriminate (𝚒𝚏-𝚝𝚑𝚎𝚗 p p₁ e₃) (𝚒𝚏₁ q e₂ e₄) = discriminate p q
  discriminate (𝚒𝚏-𝚝𝚑𝚎𝚗 p p₁ e₃) (𝚒f₂ p₀ q e₄) = discriminate p₁ q
  discriminate (𝚒𝚏-𝚝𝚑𝚎𝚗 p p₁ e₃) (𝚒𝚏₃ p₀ e₂ q) with deterministic p p₀
  ... | ()
  discriminate (𝚒𝚏-𝚎𝚕𝚜𝚎 p e₂ p₁) (𝚒𝚏₁ q e₃ e₄) = discriminate p q
  discriminate (𝚒𝚏-𝚎𝚕𝚜𝚎 p e₂ p₁) (𝚒f₂ p₀ q e₃) with deterministic p p₀
  ... | ()
  discriminate (𝚒𝚏-𝚎𝚕𝚜𝚎 p e₂ p₁) (𝚒𝚏₃ p₀ e₃ q) = discriminate p₁ q
  discriminate (try-ok p e₂) (try-rethrow q q₁) = discriminate p q
  discriminate (try-catch x p) (try-rethrow q q₁) = discriminate p q₁
  discriminate (𝚝𝚎𝚜𝚝 p) (𝚝𝚎𝚜𝚝-error q) = discriminate p q

  deterministic : ∀ {T : Type} {e : ⊢ T} {v₁ v₂ : ⊨ T} → e ⇓ v₁ → e ⇓ v₂ → v₁ ≡ v₂
  deterministic (` _) (` _) = reflexive
  deterministic (p₁ ⊞ p₂) (q₁ ⊞ q₂) with deterministic p₁ q₁ | deterministic p₂ q₂
  ... | reflexive | reflexive = reflexive
  deterministic (𝚒𝚏-𝚝𝚑𝚎𝚗 p₁ p₂ e₃) (𝚒𝚏-𝚝𝚑𝚎𝚗 q₁ q₂ e₄) = deterministic p₂ q₂
  deterministic (𝚒𝚏-𝚎𝚕𝚜𝚎 p₁ e₂ p₃) (𝚒𝚏-𝚎𝚕𝚜𝚎 q₁ e₃ q₃) = deterministic p₃ q₃
  deterministic (𝚒𝚏-𝚝𝚑𝚎𝚗 p₁ p₂ e₃) (𝚒𝚏-𝚎𝚕𝚜𝚎 q₁ e₂ q₃) with deterministic p₁ q₁ 
  ... | ()
  deterministic (𝚒𝚏-𝚎𝚕𝚜𝚎 p₁ e₂ p₃) (𝚒𝚏-𝚝𝚑𝚎𝚗 q₁ q₂ e₃) with deterministic p₁ q₁ 
  ... | ()
  deterministic (try-ok t e₂) (try-ok u e₃) = deterministic t u
  deterministic (try-ok t e₂) (try-catch x u) = ex-falso (discriminate t x)
  deterministic (try-catch x t) (try-ok u e₂) = ex-falso (discriminate u x)
  deterministic (try-catch x t) (try-catch x₁ u) = deterministic t u
  deterministic (𝚝𝚎𝚜𝚝 p) (𝚝𝚎𝚜𝚝 q) with deterministic p q
  ... | reflexive = reflexive

total? : ∀ {T : Type} (e : ⊢ T) → ∃ (λ v → e ⇓ v) ⊎ (e ⇑)
total? (` x) = ok (x , ` x)
total? (𝚒𝚏 e 𝚝𝚑𝚎𝚗 e₁ 𝚎𝚕𝚜𝚎 e₂) with total? e | total? e₁ | total? e₂
... | ok (false , p₁) | _ | ok (v , p₃) = ok (v , 𝚒𝚏-𝚎𝚕𝚜𝚎 p₁ e₁ p₃)
... | ok (false , p₁) | _ | err y = err (𝚒𝚏₃ p₁ e₁ y)
... | ok (true , p₁) | ok (fst , snd) | _ = ok (fst , 𝚒𝚏-𝚝𝚑𝚎𝚗 p₁ snd e₂)
... | ok (true , p₁) | err y | _ = err (𝚒f₂ p₁ y e₂)
... | err p           | _ | _ = err (𝚒𝚏₁ p e₁ e₂)
total? (e₁ ⊞ e₂) with total? e₁ | total? e₂
... | ok (fst , snd) | ok (fst₁ , snd₁) = ok (fst + fst₁ , snd ⊞ snd₁)
... | ok (fst , snd) | err y = err (snd ⊞₂ y)
... | err y | ok x = err (_⊞₁_ y)
... | err y | err y₁ = err (_⊞₁_ y)

total? (𝚝𝚎𝚜𝚝 e) with total? e
... | ok (fst , snd) = ok (test fst , 𝚝𝚎𝚜𝚝 snd)
... | err y = err (𝚝𝚎𝚜𝚝-error y)

total? throw = err throw-error
total? (try e catch h) with total? e | total? h
... | ok (fst , snd) | hh = ok (fst , try-ok snd h)
... | err y | ok (fst , snd) = ok (fst , try-catch y snd)
... | err y | err y₁ = err (try-rethrow y y₁)
\end{code}


