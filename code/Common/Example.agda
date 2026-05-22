module Common.Example where
open import Relation.Binary.PropositionalEquality

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

n+0≡n : (n : ℕ) → n + zero ≡ n
n+0≡n zero    = refl
n+0≡n (suc n) rewrite n+0≡n n = refl

n+sm≡n : (n m : ℕ) → n + suc m ≡ suc (n + m)
n+sm≡n zero    m = refl
n+sm≡n (suc n) m rewrite n+sm≡n n m = refl

+-commutative : (n m : ℕ) → n + m ≡ m + n
+-commutative zero    m rewrite n+0≡n m = refl
+-commutative (suc n) m rewrite +-commutative n m = sym (n+sm≡n m n)
