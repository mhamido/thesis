\begin{code}
module LambdaErr where

open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_) renaming (inj₁ to ret; inj₂ to raised)
\end{code}

\begin{code}
data Type : Set where
  -- Bool : Type
  Nat  : Type
  _⇒_  : Type → Type → Type

infixr 20 _⇒_
\end{code}

Importing contexts and environments
\begin{code}
open import Context Type public
\end{code}


\begin{code}
private variable
  T T₁ T₂ Answer : Type
  Γ Δ : Context
\end{code}

\begin{code}
data _⊢_ : Context → Type → Set where
  -- True         : Γ ⊢ Bool
  -- False        : Γ ⊢ Bool
  -- If_Then_Else : Γ ⊢ Bool → Γ ⊢ T → Γ ⊢ T → Γ ⊢ T
  
  Num : ℕ → Γ ⊢ Nat
  _⊕_ : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Nat
  -- _⊝_ : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Nat
  -- _≈_ : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Bool
  
  Var : T ∈ Γ → Γ ⊢ T
  ƛ_  : (Γ , T₁) ⊢ T₂ → Γ ⊢ (T₁ ⇒ T₂)
  _·_ : Γ ⊢ (T₁ ⇒ T₂) → Γ ⊢ T₁ → Γ ⊢ T₂

  raise : Γ ⊢ T
  try_catch_ : Γ ⊢ T → Γ ⊢ T → Γ ⊢ T

infixl 10 _·_
\end{code}

Values and environments have to be defined mutually because a closure
depends on an environment and vice versa.
\begin{code}
mutual 
  data Value : Type → Set where
    -- Bool     : 𝔹 → Value Bool
    Nat      : ℕ → Value Nat
    Closure  : Environment Γ → (Γ , T₁) ⊢ T₂ → Value (T₁ ⇒ T₂)
    
  open import Environment Type Value public
\end{code}

Evaluating a term results in either a value or an exception.
\begin{code}
data Exception : Type → Set where
  error : {T : Type} → Exception T

Result : (T : Type) → Set
Result T = Value T ⊎ Exception T
\end{code}


\begin{code}
private variable
  e e₁ e₂ e₃ : Γ ⊢ T
  v v₁ v₂ : Value T
  n n₁ n₂ : Value Nat
  δ : Environment Γ
  δ' : Environment Δ
\end{code}

Some helper definitions
\begin{code}
-- true : Value Bool
-- true = (Bool Data.Bool.true)

-- false : Value Bool
-- false = (Bool Data.Bool.false)

infixl 6 _+_ _∸_

_+_ : Value Nat → Value Nat → Value Nat
Nat a + Nat b = Nat (a Data.Nat.+ b)

_∸_ : Value Nat → Value Nat → Value Nat
Nat a ∸ Nat b = Nat (a Data.Nat.∸ b)

-- _≡ₙ_ : Value Nat → Value Nat → Value Bool
-- Nat 0 ≡ₙ Nat 0 = Bool 𝔹.true
-- Nat 0 ≡ₙ Nat (ℕ.suc b) = Bool 𝔹.false
-- Nat (ℕ.suc a) ≡ₙ Nat 0 = Bool 𝔹.false
-- Nat (ℕ.suc a) ≡ₙ Nat (ℕ.suc b) = Nat a ≡ₙ Nat b
\end{code}

Big-step semantics with environments
\begin{code}
mutual
  _⊢_⇓_ : Environment Γ → Γ ⊢ T → Value T → Set
  δ ⊢ e ⇓ v = δ ⊢ e ⇓ˢ (ret v)

  _⊢_⇓ᵉ_ : Environment Γ → Γ ⊢ T → Exception T → Set
  δ ⊢ e ⇓ᵉ v = δ ⊢ e ⇓ˢ (raised v)
  
  data _⊢_⇓ˢ_ : Environment Γ → Γ ⊢ T → Result T → Set where
    RAISE : δ ⊢ raise ⇓ᵉ (error {T})
    NUM   : ∀ n → δ ⊢ (Num n) ⇓ (Nat n)
    VAR   : ∀ (v : T ∈ Γ) → δ ⊢ (Var v) ⇓ lookupₑ δ v 
    FUN   : ∀ {δ : Environment Γ} → (e : (Γ , T₁) ⊢ T₂) → δ ⊢ (ƛ e) ⇓ (Closure δ e)

    ADD   : δ ⊢ e₁ ⇓ n₁ → δ ⊢ e₂ ⇓ n₂ → δ ⊢ (e₁ ⊕ e₂) ⇓ (n₁ + n₂)
    
    ADDₑ₁ : δ ⊢ e₁ ⇓ᵉ error
          --------------------
          → δ ⊢ (e₁ ⊕ e₂) ⇓ᵉ error

    ADDₑ₂ : δ ⊢ e₁ ⇓ n₁
          → δ ⊢ e₂ ⇓ᵉ error
          --------------------
          → δ ⊢ (e₁ ⊕ e₂) ⇓ᵉ error

    APP   : ∀ {δ' : Environment Δ} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {e : (Δ , T₁) ⊢ T₂} {v₂ : Value T₁}
            → δ ⊢ e₁ ⇓ (Closure δ' e)
            → δ ⊢ e₂ ⇓ v₂
            → ((δ' , v₂) ⊢ e ⇓ v)
            → δ ⊢ (e₁ · e₂) ⇓ v

    APPₑ₁ : ∀ {δ' : Environment Δ} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {e : (Δ , T₁) ⊢ T₂} {v₂ : Value T₁}
          → δ ⊢ e₁ ⇓ᵉ error {T₁ ⇒ T₂}
          -- → δ ⊢ e₂ ⇓ v₂
          -- → ((δ' , v₂) ⊢ e ⇓ v)
          ------------------------
          → δ ⊢ (e₁ · e₂) ⇓ᵉ error {T₂}

    APPₑ₂ : ∀ {δ' : Environment Δ} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {e : (Δ , T₁) ⊢ T₂} {v₂ : Value T₁}
          → δ ⊢ e₁ ⇓ (Closure δ' e)
          → δ ⊢ e₂ ⇓ᵉ error
          -- → ((δ' , v₂) ⊢ e ⇓ v)
          ------------------------
          → δ ⊢ (e₁ · e₂) ⇓ᵉ error {T₂}

    APPₑ₃ : ∀ {δ' : Environment Δ} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {e : (Δ , T₁) ⊢ T₂} {v₂ : Value T₁}
          → δ ⊢ e₁ ⇓ (Closure δ' e)
          → δ ⊢ e₂ ⇓ v₂
          -- → ((δ' , v₂) ⊢ e ⇓ v)
          ------------------------
          → δ ⊢ (e₁ · e₂) ⇓ᵉ error {T₂}

    APPₑ₄ : ∀ {δ' : Environment Δ} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {e : (Δ , T₁) ⊢ T₂} {v₂ : Value T₁}
          → δ ⊢ e₁ ⇓ (Closure δ' e)
          → δ ⊢ e₂ ⇓ v₂
          → (δ' , v₂) ⊢ e ⇓ᵉ error
          --------------------
          → δ ⊢ (e₁ · e₂) ⇓ᵉ error

    TRY : δ ⊢ e₁ ⇓ v
        -------------
        → δ ⊢ (try e₁ catch e₂) ⇓ v 

    TRY₁ : δ ⊢ e₁ ⇓ᵉ error
         → δ ⊢ e₂ ⇓  v
         -------------
         → δ ⊢ (try e₁ catch e₂) ⇓ v

    TRY₂ : δ ⊢ e₁ ⇓ᵉ error
         → δ ⊢ e₂ ⇓ᵉ error
         -------------
         → δ ⊢ (try e₁ catch e₂) ⇓ᵉ error
\end{code}

--------------------------------------------------------------------------------
-- Machine definition
--------------------------------------------------------------------------------

A hole is just a placeholder for some value
\begin{code}
data Hole : Set where
  ◌ : Hole
\end{code}
Stack frames with explicit holes
\begin{code}
data Frame : Type → Type → Set where
  -- If₁_Then_Else_ : Hole → Γ ⊢ T → Γ ⊢ T → Frame T Bool
  -- If₂_Then_Else_ : δ ⊢ e ⇓ true → Hole → Γ ⊢ T → Frame T T
  -- If₃_Then_Else_ : δ ⊢ e ⇓ false → Γ ⊢ T → Hole → Frame T T
  _⊕₁_           : Hole → Γ ⊢ Nat → Frame Nat Nat
  _⊕₂_           : δ ⊢ e ⇓ n → Hole → Frame Nat Nat
  _⊝₁_           : Hole → Γ ⊢ Nat → Frame Nat Nat
  _⊝₂_           : δ ⊢ e ⇓ n → Hole → Frame Nat Nat
  -- _≈₁_           : Hole → Γ ⊢ Nat → Frame Bool Nat
  -- _≈₂_           : δ ⊢ e ⇓ n → Hole → Frame Bool Nat
  -- Interestingly _·_ has only two arguments but 3 sub-trees, thus we need 3 frames
  -- Since we don't know the expression we get from the closure we technically have
  -- 2 holes in one frame
  App₁           : Hole → Γ ⊢ T₁ → Frame T (T₁ ⇒ T₂)
  App₂           : δ ⊢ e₁ ⇓ v₁ → Hole → Frame T T₁
  App₃           : δ ⊢ e₁ ⇓ v₁ → δ ⊢ e₂ ⇓ v₂ → Hole → Frame T T₁

  Try₁ : Hole → Γ ⊢ T → Frame T T
  Try₂ : δ ⊢ e₁ ⇓ᵉ error → Hole → Frame T T
  -- todo: is this necessary? 
  Try₃ : δ ⊢ e₁ ⇓ᵉ error → δ ⊢ e₂ ⇓ᵉ error → Frame T T
\end{code}

Stack
\begin{code}
data Stack (Answer : Type) : Type → Set where
  []  : Stack Answer Answer
  _∷_ : Stack Answer T₁ → Frame T₁ T₂ → Stack Answer T₂
\end{code}

Machine state
Going up the tree, aka. eval: ↑
Going down the tree, aka. return: ↓
\begin{code}
private variable
  r : Result T

data State (Answer : Type) : Set where
  _⊢_↓_ : {Γ : Context} → (δ : Environment Γ) → Stack Answer T → {e : Γ ⊢ T} → δ ⊢ e ⇓ˢ r → State Answer
  _⊢_↑_ : (δ : Environment Γ) → Stack Answer T → Γ ⊢ T → State Answer
\end{code}

Step relation
\begin{code}
data _⇾_ : State T → State T → Set where
  step-Var       : ∀ {v : T ∈ Γ} {stack : Stack Answer T}
                   → (δ ⊢ stack ↑ Var v) ⇾ (δ ⊢ stack ↓ VAR v)

  step-ƛ         : ∀ {stack : Stack Answer (T₁ ⇒ T₂)} {e : (Γ , T₁) ⊢ T₂} {δ : Environment Γ}
                  → (δ ⊢ stack ↑ (ƛ e)) ⇾ (δ ⊢ stack ↓ FUN e)

  step-Num       : ∀ {n : ℕ} {stack : Stack Answer Nat}
                   → (δ ⊢ stack ↑ Num n) ⇾ (δ ⊢ stack ↓ NUM n)
                
  step-⊕         : ∀ {e₁ e₂ : Γ ⊢ Nat} {stack : Stack Answer Nat}
                   → (δ ⊢ stack ↑ (e₁ ⊕ e₂)) ⇾ (δ ⊢ (stack ∷ (◌ ⊕₁ e₂)) ↑ e₁)

  step-⊕₁        : ∀ {e₁ e₂ : Γ ⊢ Nat} {p₁ : δ ⊢ e₁ ⇓ n₁} {stack : Stack Answer Nat}
                   → (δ ⊢ (stack ∷ (◌ ⊕₁ e₂)) ↓ p₁) ⇾ (δ ⊢ (stack ∷ (p₁ ⊕₂ ◌)) ↑ e₂)

  step-⊕₂        : ∀ {e₁ e₂ : Γ ⊢ Nat} {p₁ : δ ⊢ e₁ ⇓ n₁} {p₂ : δ ⊢ e₂ ⇓ n₂} {stack : Stack Answer Nat}
                   → (δ ⊢ (stack ∷ (p₁ ⊕₂ ◌)) ↓ p₂) ⇾ (δ ⊢ stack ↓ ADD p₁ p₂)

  step-App       : ∀ {stack : Stack Answer T₂}
                   → (δ ⊢ stack ↑ (e₁ · e₂)) ⇾ (δ ⊢ (stack ∷ (App₁ ◌ e₂)) ↑ e₁)

  step-App₁    : ∀ {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {δ' : Environment Δ} {e : (Δ , T₁) ⊢ T₂} {e₂ : Γ ⊢ T₁} {p₁ : δ ⊢ e₁ ⇓ (Closure δ' e)} {stack : Stack Answer T₂}
                 → (δ ⊢ stack ∷ (App₁ ◌ e₂) ↓ p₁) ⇾ (δ ⊢ stack ∷ (App₂ p₁ ◌) ↑ e₂)
  
  step-App₂    : ∀ {stack : Stack Answer T₂} {δ' : Environment Δ} {e : (Δ , T₁) ⊢ T₂} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {v₂ : Value T₁} {p₁ : δ ⊢ e₁ ⇓ (Closure δ' e)} {p₂ : δ ⊢ e₂ ⇓ v₂}
                 → (δ ⊢ stack ∷ (App₂ p₁ ◌) ↓ p₂) ⇾ ((δ' , v₂) ⊢ stack ∷ (App₃ p₁ p₂ ◌) ↑ e)
  
  step-App₃    : ∀ {stack : Stack Answer T₂} {δ' : Environment Δ} {e : (Δ , T₁) ⊢ T₂} {v : Value T₂} {e₁ : Γ ⊢ (T₁ ⇒ T₂)} {v₂ : Value T₁} {p₃ : (δ' , v₂) ⊢ e ⇓ v} {p₁ : δ ⊢ e₁ ⇓ (Closure δ' e)} {p₂ : δ ⊢ e₂ ⇓ v₂}
                 → ((δ' , v₂) ⊢ stack ∷ (App₃ p₁ p₂ ◌) ↓ p₃) ⇾ (δ ⊢ stack ↓ (APP p₁ p₂ p₃))

  step-Raise : ∀ {stack : Stack Answer T}
            → (δ ⊢ stack ↑ raise) ⇾ (δ ⊢ stack ↓ RAISE)
  
  step-Try : ∀ {stack : Stack Answer _ }
           → (δ ⊢ stack ↑ (try e₁ catch e₂)) ⇾ (δ ⊢ stack ∷ (Try₁ ◌ e₂) ↑ e₁)
  
  step-Try₁ : ∀ {stack : Stack Answer _ } {p₁ : δ ⊢ e₁ ⇓ v₁}
           → (δ ⊢ stack ∷ (Try₁ ◌ e₂) ↑ e₁) ⇾ (δ ⊢ stack ↓ TRY {e₂ = e₂} p₁)
  
  step-Try₂ : ∀ {stack : Stack Answer _ } {p₁ : δ ⊢ e₁ ⇓ᵉ error}
            → (δ ⊢ stack ∷ (Try₁ ◌ e₂) ↓ p₁) ⇾ (δ ⊢ stack ∷ Try₂ p₁ ◌ ↑ e₂)
  
  step-Tryₑ : ∀ {stack : Stack Answer _} {p₁ : δ ⊢ e₁ ⇓ᵉ error} {p₂ : δ ⊢ e₂ ⇓ v}
            → (δ ⊢ stack ∷ Try₁ ◌ e₂ ↑ e₁) ⇾ (δ ⊢ stack ∷ Try₂ p₁ ◌ ↓ p₂)
  
  step-Try₃ : ∀ {stack : Stack Answer _ } {p₁ : δ ⊢ e₁ ⇓ᵉ error} {p₂ : δ ⊢ e₂ ⇓ v₂ }
            → (δ ⊢ stack ∷ Try₂ p₁ ◌ ↓ p₂) ⇾ (δ ⊢ stack ↓ TRY₁ p₁ p₂)

  step-Try₄ : ∀ {stack : Stack Answer _ } {p₁ : δ ⊢ e₁ ⇓ᵉ error} {p₂ : δ ⊢ e₂ ⇓ᵉ error}
            → (δ ⊢ stack ∷ (Try₂ p₁ ◌) ↓ p₂) ⇾ (δ ⊢ stack ↓ TRY₂ p₁ p₂)

  -- rule only applicable if there's an exception raised:
  -- step-PopFrame : ∀ {stack : Stack Answer T} {f : Frame T₁ T} {δ : Environment Γ} {e : Γ ⊢ T₁} {r : Result T₁}
  --                 → (δ ⊢ (stack ∷ f) 
  -- step-Try₅ : 

  
\end{code}

Transitive, reflexive closure of the step relation
\begin{code}
data _↠_ : State T → State T → Set where
  base  : ∀ {s : State T}        → s ↠ s
  step  : ∀ {s₁ s₂ s₃ : State T} → s₁ ⇾ s₂ → s₂ ↠ s₃ → s₁ ↠ s₃

↠-reflexive : ∀ {s : State Answer} → s ↠ s
↠-reflexive = base

↠-transitive : ∀ {s₀ s₁ s₂ : State Answer} → s₀ ↠ s₁ → s₁ ↠ s₂ → s₀ ↠ s₂
↠-transitive (base)      q = q
↠-transitive (step s p)  q = step s (↠-transitive p q)
\end{code}

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

\begin{code}
infix  0 proof_
infixr 1 ⇾-link ↠-link
infix  2 _∎

proof_ : {s₁ s₂ : State Answer} → s₁ ↠ s₂ → s₁ ↠ s₂
proof s₁⇾⃰s₂ = s₁⇾⃰s₂

syntax ⇾-link x q p = x ⇾⟨ p ⟩ q
⇾-link : (s₀ : State Answer) {s₁ s₂ : State Answer} → s₁ ↠ s₂ → s₀ ⇾ s₁ → s₀ ↠ s₂
⇾-link _ q p = step p q

syntax ↠-link x q p = x ↠⟨ p ⟩ q
↠-link : (s₀ : State Answer) {s₁ s₂ : State Answer} → s₁ ↠ s₂ → s₀ ↠ s₁ → s₀ ↠ s₂
↠-link _ q p = ↠-transitive p q

_∎ : (s : State Answer) → s ↠ s
e ∎ = ↠-reflexive
\end{code}


Trivial proof of correctness
\begin{code}
correct : ∀ (e : Γ ⊢ T) → (v : Value T) → (p : δ ⊢ e ⇓ v) →
  (δ ⊢ [] ↑ e) ↠ (δ ⊢ [] ↓ p) → δ ⊢ e ⇓ v
correct _ _ p _ = p
\end{code}

Completeness
\begin{code}
complete : ∀ (δ : Environment Γ) (stack : Stack Answer T) (e : Γ ⊢ T) (v : Value T) →
  (p : δ ⊢ e ⇓ v) → (δ ⊢ stack ↑ e) ↠ (δ ⊢ stack ↓ p)
-- complete : ∀ (δ : Environment Γ) (stack : Stack Answer T) (e : Γ ⊢ T) (v : Result T) →
  -- (p : δ ⊢ e ⇓ˢ v) → (δ ⊢ stack ↑ e) ↠ (δ ⊢ stack ↓ p)
complete δ stack (Num x) v (NUM .x) = step step-Num base
complete δ stack (Var x) v (VAR x₁) = step step-Var base
complete δ stack (e₁ ⊕ e₂) v (ADD p₁ p₂) =
  proof
    (δ ⊢ stack ↑ (e₁ ⊕ e₂))
  ⇾⟨ step-⊕ ⟩
    (δ ⊢ (stack ∷ (◌ ⊕₁ e₂)) ↑ e₁)
  ↠⟨ complete δ (stack ∷ (◌ ⊕₁ e₂)) e₁ _ p₁ ⟩
    (δ ⊢ (stack ∷ (◌ ⊕₁ e₂)) ↓ p₁)
  ⇾⟨ step-⊕₁ ⟩
    (δ ⊢ (stack ∷ (p₁ ⊕₂ ◌)) ↑ e₂)
  ↠⟨ complete δ (stack ∷ (p₁ ⊕₂ ◌)) e₂ _ p₂ ⟩
    (δ ⊢ (stack ∷ (p₁ ⊕₂ ◌)) ↓ p₂)
  ⇾⟨ step-⊕₂ ⟩
    (δ ⊢ stack ↓ ADD p₁ p₂)
  ∎
complete δ stack (ƛ e) v (FUN e) = step step-ƛ base
complete δ stack (e₁ · e₂) v (APP {δ' = δ'} {e = e} {v₂ = v₂} p₁ p₂ p₃) =
  proof
    (δ ⊢ stack ↑ (e₁ · e₂))
  ⇾⟨ step-App ⟩
    (δ ⊢ stack ∷ (App₁ ◌ e₂) ↑ e₁)
  ↠⟨ complete δ (stack ∷ (App₁ ◌ e₂)) e₁ _ p₁ ⟩
    (δ ⊢ stack ∷ (App₁ ◌ e₂) ↓ p₁)
  ⇾⟨ step-App₁ ⟩
    (δ ⊢ stack ∷ (App₂ p₁ ◌) ↑ e₂)
  ↠⟨ complete δ (stack ∷ (App₂ p₁ ◌)) e₂ _ p₂ ⟩
    (δ ⊢ stack ∷ (App₂ p₁ ◌) ↓ p₂)
  ⇾⟨ step-App₂ ⟩
    ((δ' , v₂) ⊢ stack ∷ App₃ p₁ p₂ ◌ ↑ e)
  ↠⟨ complete (δ' , v₂) (stack ∷ (App₃ p₁ p₂ ◌)) e _ p₃ ⟩
    ((δ' , v₂) ⊢ stack ∷ (App₃ p₁ p₂ ◌) ↓ p₃)
  ⇾⟨ step-App₃ ⟩
    (δ ⊢ stack ↓ APP p₁ p₂ p₃)
  ∎ 
complete δ stack (try e₁ catch e₂) v (TRY p₁) = 
  proof
    δ ⊢ stack ↑ (try e₁ catch e₂)
  ⇾⟨ step-Try ⟩
    δ ⊢ stack ∷ Try₁ ◌ e₂ ↑ e₁
  ⇾⟨ step-Try₁ ⟩
    δ ⊢ stack ↓ TRY p₁
  ∎
complete δ stack (try e₁ catch e₂) v (TRY₁ p₁ p₂) = 
  proof
    δ ⊢ stack ↑ (try e₁ catch e₂)
  ⇾⟨ step-Try ⟩
    δ ⊢ stack ∷ Try₁ ◌ e₂ ↑ e₁
  ⇾⟨ step-Tryₑ ⟩
    δ ⊢ stack ∷ Try₂ p₁ ◌ ↓ p₂
  ⇾⟨ step-Try₃ ⟩
    δ ⊢ stack ↓ TRY₁ p₁ p₂
  ∎
\end{code}