\begin{code}
module MiniSquared.Recursion where

open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹) hiding (_<?_; T)
open import Data.String

infixr 7 _⇒_
infix 4 _⊢_
infixr 4 _·_

data Type : Set where
  Nat : Type
  Bool : Type
  _⇒_  : Type → Type → Type

open import MiniSquared.Context Type

private variable
  T T' U V : Type
  T₁ T₂ T₃ : Type
  n m  : ℕ
  b    : 𝔹
  Γ    : Context

-- A binary operation has two argument types and a result type
data BinaryOp : Type → Type → Type → Set where
  Add : BinaryOp Nat Nat Nat
  Lt  : BinaryOp Nat Nat Bool
  Eq  : BinaryOp Nat Nat Bool

data _⊢_ : Context → Type → Set where
  Num              : ℕ → Γ ⊢ Nat
  _[_]_            : Γ ⊢ T → BinaryOp T U V → Γ ⊢ U → Γ ⊢ V
  False            : Γ ⊢ Bool
  True             : Γ ⊢ Bool
  If_Then_Else_    : Γ ⊢ Bool → Γ ⊢ T → Γ ⊢ T → Γ ⊢ T
  Var              : T ∈ Γ → Γ ⊢ T
  Let_In_          : Γ ⊢ T₁ → (Γ , T₁) ⊢ T₂ → Γ ⊢ T₂
  Fun_             : (Γ , T₁) ⊢ T₂ → Γ ⊢ (T₁ ⇒ T₂)
  _·_              : Γ ⊢ (T₁ ⇒ T₂) → Γ ⊢ T₁ → Γ ⊢ T₂
  LetRec_·_≈_In_   : (T₁ ⇒ T₂) ∈ Γ → T₁ ∈ Γ → (Γ , T₁) ⊢ T₂ → (Γ , T₁ ⇒ T₂) ⊢ T₃ → Γ ⊢ T₃


mutual

  data Value : Type → Set where
    Nat  : ℕ → Value Nat
    Bool : 𝔹 → Value Bool
    Closure : Environment Γ → (Γ , T₁) ⊢ T₂ → Value (T₁ ⇒ T₂)

  open import MiniSquared.Environment Type Value


-- Interpretation of binary operations
_⟦_⟧_ : Value T -> BinaryOp T U V -> Value U -> Value V
(Nat v₁) ⟦ Add ⟧ (Nat v₂) = Nat  (v₁ + v₂)
(Nat v₁) ⟦ Lt ⟧  (Nat v₂) = Bool (v₁ <ᵇ v₂)
(Nat v₁) ⟦ Eq ⟧  (Nat v₂) = Bool (v₁ ≡ᵇ v₂)

data Frame : Type → Type → Set where
  Bin₁ : Environment Γ → BinaryOp T U V → Γ ⊢ U → Frame T V
  Bin₂ : Value T → BinaryOp T U V → Frame U V
  If₁  : Environment Γ → Γ ⊢ T → Γ ⊢ T → Frame Bool T
  Let₁ : Environment Γ → (Γ , T₁) ⊢ T₂ → Frame T₁ T₂
  App₁ : Environment Γ → Γ ⊢ T₁ → Frame (T₁ ⇒ T₂) T₂

data Stack : Type → Type → Set where
  ∅   : Stack T T
  _∷_ : Frame T U → Stack U V → Stack T V

data State : Type → Set where
  Eval : Environment Γ → Γ ⊢ T → Stack T V → State V
  Ret  : Value T → Stack T V → State V

step : State V -> State V
step (Eval δ (Num n) stack) = Ret (Nat n) stack
step (Eval δ (e₁ [ op ] e₂) stack) = Eval δ e₁ (Bin₁ δ op e₂ ∷ stack)
step (Eval δ False stack) = Ret (Bool false) stack
step (Eval δ True stack) = Ret (Bool true) stack
step (Eval δ (If e₁ Then e₂ Else e₃) stack) = Eval δ e₁ (If₁ δ e₂ e₃ ∷ stack)
step (Eval δ (Var v) stack) = Ret (lookupₑ δ v) stack
step (Eval δ (Let v In e) stack) = Eval δ v (Let₁ δ e ∷ stack)
step (Eval δ (Fun e) stack) = Ret (Closure δ e) stack
step (Eval δ (f · e) stack) = Eval δ f (App₁ δ e ∷ stack)
step (Eval δ (LetRec f · x ≈ e In e') stack) = Eval δ' e' stack
  where
    mutual
      δ' = δ , c
      c = Closure δ' {!e!}
step (Ret v ∅) = Ret v ∅
step (Ret v₁ (Bin₁ δ op e₂ ∷ stack)) = Eval δ e₂ (Bin₂ v₁ op ∷ stack)
step (Ret v₂ (Bin₂ v₁ op ∷ stack)) = Ret (v₁ ⟦ op ⟧ v₂) stack
step (Ret (Bool b) (If₁ δ e₂ e₃ ∷ stack)) = if b then Eval δ e₂ stack else Eval δ e₃ stack
step (Ret v (Let₁ δ e ∷ stack)) = Eval (δ , v) e stack
step (Ret (Closure δ' f) (App₁ δ e ∷ stack)) = Eval δ e (Let₁ δ' f ∷ stack)
\end{code}
