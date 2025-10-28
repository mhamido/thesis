--------------------------------------------------------------------------------
-- This module adds an evaluator (i.e, denotational semantics) for our language. 
-- This is primarily meant to be used to generate proofs of e ⇓ v out of 
-- convenience.
--------------------------------------------------------------------------------

\begin{code}
open import Data.Bool renaming (Bool to 𝔹) using ()
open import Data.Nat using (ℕ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong-app; subst)
open import Data.Empty using (⊥) renaming (⊥-elim to ex-falso)
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟪_,_⟫)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)

open import Milli
-- open import Environment Type Value
-- open import Context Type
\end{code}

--------------------------------------------------------------------------------
-- Some useful definitions.
--------------------------------------------------------------------------------
\begin{code}
-- liftA{1, 2, 3} style functions, but with a trailing lambda.
liftA1 : {A B : Set} → Maybe A → (A → B) → Maybe B
liftA1 (just x) f = just (f x)
liftA1  nothing f = nothing

-- liftA2 with a trailing lambda.
liftA2 : {A B C : Set} → Maybe A → Maybe B → (A → B → C) → Maybe C
liftA2 (just x) (just y) f = just (f x y)
liftA2 (just x) nothing  f = nothing
liftA2 nothing         b f = nothing

liftA3 : {A B C D : Set} → Maybe A → Maybe B → Maybe C → (A → B → C → D) → Maybe D
liftA3 (just x) (just y) (just z) f = just (f x y z)
liftA3 (just x) (just y) nothing f = nothing
liftA3 (just x) nothing (just z) f = nothing
liftA3 (just x) nothing nothing f = nothing
liftA3 nothing (just y) (just z) f = nothing
liftA3 nothing (just y) nothing f = nothing
liftA3 nothing nothing (just z) f = nothing
liftA3 nothing nothing nothing f = nothing
\end{code}


--------------------------------------------------------------------------------
-- The evaluation function:
--------------------------------------------------------------------------------

\begin{code}
eval : ∀ (fuel : ℕ) {Γ T} (δ : Environment Γ) 
     → (e : Γ ⊢ T)
     → Maybe (∃[ v ] (δ ⊢ e ⇓ v))
eval    ℕ.zero δ       e    = nothing
eval (ℕ.suc n) δ (Num x)    = just ⟪ Nat x , NUM x ⟫
eval (ℕ.suc n) δ    True    = just ⟪ Bool 𝔹.true , TRUE ⟫
eval (ℕ.suc n) δ   False    = just ⟪ Bool 𝔹.false , FALSE ⟫ 
eval (ℕ.suc n) δ      ⟨⟩    = just ⟪ Unit , UNIT ⟫
eval (ℕ.suc n) δ (Var x)    = just ⟪ lookupₑ δ x , VAR x ⟫
eval (ℕ.suc n) δ (ƛ e)      = just ⟪ (Closure δ e) , FUN e ⟫
eval (ℕ.suc n) δ (LetRec e) = just ⟪ (RecClosure δ e) , LETREC e ⟫
eval (ℕ.suc n) δ (e₁ ⊕ e₂) =
  liftA2 (eval n δ e₁) (eval n δ e₂) λ where
    ⟪ v₁ , p₁ ⟫ ⟪ v₂ , p₂ ⟫ → ⟪ v₁ + v₂ , ADD p₁ p₂ ⟫
  
eval (ℕ.suc n) δ (e₁ ⊝ e₂) =
  liftA2 (eval n δ e₁) (eval n δ e₂) λ where
    ⟪ v₁ , p₁ ⟫ ⟪ v₂ , p₂ ⟫ → ⟪ v₁ ∸ v₂ , SUB p₁ p₂ ⟫

eval (ℕ.suc n) δ (e₁ ≈ e₂) =
  liftA2 (eval n δ e₁) (eval n δ e₂) λ where
    ⟪ v₁ , p₁ ⟫ ⟪ v₂ , p₂ ⟫ → ⟪ v₁ ≡ₙ v₂ , EQ p₁ p₂ ⟫

eval (ℕ.suc n) δ (f   · x) =
  eval n δ f >>= λ where
    ⟪ Closure    δ' e , p₁ ⟫ → do
      ⟪ x' , p₂ ⟫ ← eval n δ x
      ⟪ v  , p₃ ⟫ ← eval n (δ' , x') e
      just ⟪ v , APP p₁ p₂ p₃ ⟫
      
    ⟪ RecClosure δ' e , p₁ ⟫ → do
      ⟪ x' , p₂ ⟫ ← eval n δ x
      ⟪ v  , p₃ ⟫ ← eval n (δ' , RecClosure δ' e , x') e
      just ⟪ v , RECAPP p₁ p₂ p₃ ⟫

eval (ℕ.suc n) δ (e₁ , e₂) =
  liftA2 (eval n δ e₁) (eval n δ e₂) λ where
    ⟪ v₁ , p₁ ⟫ ⟪ v₂ , p₂ ⟫ → ⟪ (v₁ , v₂) , TUPLE p₁ p₂ ⟫

eval (ℕ.suc n) δ (If e Then e₁ Else e₂) =
  eval n δ e >>= λ where
    ⟪ Bool 𝔹.false , p ⟫ →
      liftA1 (eval n δ e₂) λ where
        ⟪ v , p₂ ⟫ → ⟪ v , IF₂ p e₁ p₂ ⟫
    ⟪ Bool 𝔹.true  , p ⟫ →
      liftA1 (eval n δ e₁) λ where
        ⟪ v , p₁ ⟫ → ⟪ v , IF₁ p p₁ e₂ ⟫

eval (ℕ.suc n) δ (Let e₁ In e₂) = do
  ⟪ v₁ , p₁ ⟫ ← eval n δ e₁
  ⟪ v₂ , p₂ ⟫ ← eval n (δ , v₁) e₂
  just ⟪ v₂ , LET p₁ p₂ ⟫
  
eval (ℕ.suc n) δ (fst e) = liftA1 (eval n δ e) λ where
  ⟪ (v , _) , p ⟫ → ⟪ v , FST p ⟫
eval (ℕ.suc n) δ (snd e) = liftA1 (eval n δ e) λ where
  ⟪ (_ , v) , p ⟫ → ⟪ v , SND p ⟫

eval (ℕ.suc n) δ (inl e) = liftA1 (eval n δ e) λ where
  ⟪ v , p ⟫ → ⟪ inl v , INL p ⟫
  
eval (ℕ.suc n) δ (inr e) = liftA1 (eval n δ e) λ where
  ⟪ v , p ⟫ → ⟪ inr v , INR p ⟫
  
eval (ℕ.suc n) δ (case e of e₁ ∣ e₂) =
  eval n δ e >>= λ where
    ⟪ inl v , p₁ ⟫ →
      liftA1 (eval n (δ , v) e₁) λ where
        ⟪ t , p₂ ⟫ → ⟪ t , CASE₁ p₁ p₂ ⟫
    ⟪ inr v , p ⟫ →
      liftA1 (eval n (δ , v) e₂) λ where
        ⟪ t , p₂ ⟫ → ⟪ t , CASE₂ p p₂ ⟫
\end{code}

\begin{code}

Factorial : ∅ ⊢ (Nat ⇒ Nat)
Factorial = LetRec (If (Var 𝟘 ≈ Num 0) Then Num 1 Else ((Var 𝟙 · ((Var 𝟘) ⊝ Num 1))))

example : ∅ ⊢ Nat
example = Factorial · Num 3

_ : eval 100 ∅ example ≡ just ⟪ {!   !} , {!   !} ⟫
_ = refl
\end{code}
