# Deriving Compilers

The language used here is the simply typed lambda calculus with naturals, products and the unit type.
- Prior work dealt with abstract machines (i.e, interpreters) derived from specifications.
    - The Abstract Machine:
        - "Tree-walking" interpreter
        - `↑` - Evaluate an expression.
        - `↓` - Evaluation returns (with a proof that the expression given evaluates to the value).
    - Model the step relation between machine states (which model _what_ sub-tree of the expression is being evaluated). 
    - Prove `correctness` (trivial), and `completeness`.

```
module Arith-DerivingCompilers where

open import Data.Nat using (ℕ)
open import Data.Bool renaming (Bool to 𝔹) hiding (T)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
```

```
data Type : Set where
    Bool : Type
    Nat : Type
    Unit : Type
    _⇒_ : Type → Type → Type
    _×_ : Type → Type → Type

infixr 20 _⇒_
```

```
open import Context Type public

private variable
    T T₁ T₂ T₃ : Type
    Γ Δ : Context


data _⊢_ : Context → Type → Set where
    Num          : ℕ → Γ ⊢ Nat
    Bool         : 𝔹 → Γ ⊢ Bool
    ⟨⟩           : Γ ⊢ Unit
    _⊕_          : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Nat
    Var          : T ∈ Γ → Γ ⊢ T
    ƛ_           : (Γ , T₁) ⊢ T₂ → Γ ⊢ (T₁ ⇒ T₂)
    _·_          : Γ ⊢ (T₁ ⇒ T₂) → Γ ⊢ T₁ → Γ ⊢ T₂
    _,_          : Γ ⊢ T₁ → Γ ⊢ T₂ → Γ ⊢ (T₁ × T₂)
    Outl         : Γ ⊢ (T₁ × T₂) → Γ ⊢ T₁
    Outr         : Γ ⊢ (T₁ × T₂) → Γ ⊢ T₂

mutual
    data Value : Type → Set where
        Unit : Value Unit
        Nat      : ℕ → Value Nat
        Bool     : 𝔹 → Value Bool
        _,_      : Value T₁ → Value T₂ → Value (T₁ × T₂)
        Closure  : Environment Γ → (Γ , T₁) ⊢ T₂ → Value (T₁ ⇒ T₂)
    
    open import Environment Type Value public
```

# Big-Step Semantics

```
private variable
  e e₁ e₂ e₃ : Γ ⊢ T
  v v₁ v₂ : Value T
  n n₁ n₂ : Value Nat
  δ : Environment Γ
  δ' : Environment Δ

infixl 6 _+_
_+_ : Value Nat → Value Nat → Value Nat
Nat a + Nat b = Nat (a Data.Nat.+ b)

data _⊢_⇓_ : Environment Γ → Γ ⊢ T → Value T → Set where
    UNIT  : δ ⊢ ⟨⟩ ⇓ Unit
    NUM   : ∀ n → δ ⊢ (Num n) ⇓ (Nat n)
    BOOL  : ∀ b → δ ⊢ (Bool b) ⇓ (Bool b)
    VAR   : ∀ (v : T ∈ Γ) → δ ⊢ (Var v) ⇓ lookupₑ δ v 
    FUN   : ∀ {δ : Environment Γ} → (e : (Γ , T₁) ⊢ T₂) → δ ⊢ (ƛ e) ⇓ (Closure δ e)
    ADD   : δ ⊢ e₁ ⇓ n₁ → δ ⊢ e₂ ⇓ n₂ → δ ⊢ (e₁ ⊕ e₂) ⇓ (n₁ + n₂)

    APP   : ∀ {δ' : Environment Δ} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {e : (Δ , T₁) ⊢ T₂} {v₂ : Value T₁}
        → δ ⊢ e₁ ⇓ (Closure δ' e)
        → δ ⊢ e₂ ⇓ v₂
        → ((δ' , v₂) ⊢ e ⇓ v)
        → δ ⊢ (e₁ · e₂) ⇓ v
    
    TUPLE  : ∀ {e₁ : Γ ⊢ T₁} {e₂ : Γ ⊢ T₂}
         → δ ⊢ e₁ ⇓ v₁
         → δ ⊢ e₂ ⇓ v₂
         -------------
         → δ ⊢ (e₁ , e₂) ⇓ (v₁ , v₂)

    OUTL    : δ ⊢ e₁ ⇓ (v₁ , v₂) → δ ⊢ Outl e₁ ⇓ v₁
    OUTR    : δ ⊢ e₁ ⇓ (v₁ , v₂) → δ ⊢ Outr e₁ ⇓ v₂
```


# Machine Code

Target Language: [Categorical Abstract Machine](/docs/lectures.pdf)

```
data Code : Type → Type → Set where
    Nop : Code T₁ T₁
    _⨾_ : Code T₁ T₂ → Code T₂ T₃ → Code T₁ T₃
    Unit : Code T₁ Unit
    Fst : Code (T₁ × T₂) T₁
    Snd : Code (T₁ × T₂) T₂
    _&&_ : Code T₁ T₂ → Code T₁ T₃ → Code T₁ (T₂ × T₃)
    Cur : Code (T₁ × T₂) T₃ → Code T₁ (T₂ ⇒ T₃)
    App : Code ((T₁ ⇒ T₂) × T₁) T₂
    Num : ℕ → Code T₁ Nat 
    Add : Code (Nat × Nat) Nat
    False : Code T₁ Bool
    True : Code T₁ Bool
    _∣∣_ : Code T₁ T₂ → Code T₁ T₂ → Code (T₁ × Bool) T₂
infixl 10 _⨾_ 
```

# Compiler
```
-- Reify the context into a type.
type : Context → Type
type ∅ = Unit
type (c , t) = type c × t

lookupᶜ : T ∈ Γ → Code (type Γ) T
lookupᶜ Z = Snd
lookupᶜ (S n) = Fst ⨾ lookupᶜ n

compile : Γ ⊢ T → Code (type Γ) T
compile ⟨⟩ = Unit
compile (Num x) = Num x
compile (Bool true) = True
compile (Bool false) = False
compile (Var n) = lookupᶜ n
compile (ƛ e) = Cur (compile e)
compile (e₁ , e₂) = compile e₁ && compile e₂
compile (e₁ ⊕ e₂) = compile e₁ && compile e₂ ⨾ Add
compile (e₁ · e₂) = compile e₁ && compile e₂ ⨾ App
compile (Outl e) = compile e ⨾ Fst
compile (Outr e) = compile e ⨾ Snd
```

# Execution Semantics for Code

The `Value` we've previously defined contains a constructor (specifically, `Closure`) with expressions.
So we define a separate value type for the target language that only contains compiled values.

```
data Valueᶜ : Type → Set where
    CUnit    : Valueᶜ Unit
    CNat     : ℕ → Valueᶜ Nat
    CBool    : 𝔹 → Valueᶜ Bool
    _,_      : Valueᶜ T₁ → Valueᶜ T₂ → Valueᶜ (T₁ × T₂)
    CClosure : Code (T₁ × T₂) T₃ → Valueᶜ T₁ → Valueᶜ (T₂ ⇒ T₃)

private variable
    cv cv₁ cv₂ : Valueᶜ T

{-# TERMINATING #-}
exec : Code T₁ T₂ → Valueᶜ T₁ → Valueᶜ T₂
exec Nop v = v
exec Unit v = CUnit
exec (Num n) v = CNat n
exec False v = CBool false
exec True v = CBool true
exec Fst (v₁ , v₂) = v₁
exec Snd (v₁ , v₂) = v₂
exec (c₁ ⨾ c₂) v = exec c₂ (exec c₁ v)
exec (c₁ && c₂) v = exec c₁ v , exec c₂ v
exec Add (CNat n₁ , CNat n₂) = CNat (n₁ Data.Nat.+ n₂)
exec (c₁ ∣∣ c₂) (v , CBool true) = exec c₁ v
exec (c₁ ∣∣ c₂) (v , CBool false) = exec c₂ v
exec (Cur c) v = CClosure c v
exec App (CClosure c env , v) = exec c (env , v)

mutual
  -- Map source values to compiled values
  convert : Value T → Valueᶜ T
  convert Unit = CUnit
  convert (Nat n) = CNat n
  convert (Bool b) = CBool b
  convert (v₁ , v₂) = convert v₁ , convert v₂
  convert (Closure env e) = CClosure (compile e) (reify env)

  -- Reify source environments into target values
  reify : Environment Γ → Valueᶜ (type Γ)
  reify {∅} [] = CUnit
  reify {_ , _} (env , v) = reify env , convert v
```

# Correctness Theorem

The compiler is correct if executing compiled code produces the same result as evaluation:

```

-- Lemma: addition commutes with conversion
add-correct : ∀ (n₁ n₂ : Value Nat) 
            → exec Add (convert n₁ , convert n₂) ≡ convert (n₁ + n₂)
add-correct (Nat n₁) (Nat n₂) = refl

{-# TERMINATING #-} -- TODO: Unfortunately arises as a result as using exec.
correct : ∀ (δ : Environment Γ) (e : Γ ⊢ T) (v : Value T) (p : δ ⊢ e ⇓ v)
        → exec (compile e) (reify δ) ≡ convert v

correct δ ⟨⟩ v UNIT = refl
correct δ (Num x) v (NUM n) = refl
correct δ (Bool false) v (BOOL b) = refl
correct δ (Bool true) v (BOOL b) = refl
correct δ (ƛ e) (Closure .δ .e) (FUN .e) = refl

correct δ (Var x) v (VAR .x) = lookup-reify _ x
    where
        lookup-reify : ∀ (δ : Environment Γ) (x : T ∈ Γ)
                     → exec (lookupᶜ x) (reify δ) ≡ convert (lookupₑ δ x)
        lookup-reify (δ , x) Z = refl
        lookup-reify (δ , x) (S n) = lookup-reify δ n

correct δ (e₁ ⊕ e₂) v (ADD {n₁ = n₁} {n₂ = n₂} p₁ p₂) 
    rewrite correct δ e₁ _ p₁
          | correct δ e₂ _ p₂
          | add-correct n₁ n₂
           = refl

correct δ (e₁ · e₂) v (APP {δ' = δ'} {e = e} {v₂ = v₂} p₁ p₂ p₃)
  rewrite correct δ e₁ (Closure δ' e) p₁
        | correct δ e₂ v₂ p₂
        | correct (δ' , v₂) e v p₃ 
        = refl

correct δ (e₁ , e₂) (v₁ , v₂) (TUPLE p₁ p₂)
  rewrite correct δ e₁ v₁ p₁
        | correct δ e₂ v₂ p₂ 
        = refl

correct δ (Outl e) v (OUTL {v₂ = v₂} p)
  rewrite correct δ e (v , v₂) p = refl

correct δ (Outr e) v (OUTR {v₁ = v₁} p)
  rewrite correct δ e (v₁ , v) p = refl
```

# Notes to self

This is essentially what was presented (and proven) in the compiler correctness chapter of the VFP course.
The question now is how do we derive `compile`?
    - Model compilation as a relation?
    - Can we prove correctness without relying on `exec`?