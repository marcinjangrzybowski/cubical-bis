module Cubical.Analysis.Real.Algebra.Natural where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)

open import Cubical.Data.Nat as ℕ
  using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as ℕOrder
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals.Base as ℚ using (fromNat)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
  using (0≤pos; ℕ+→ℚ+; ℕ·→ℚ·)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition


realNatural : ℕ → ℝ
realNatural n = rat (fromNat n)


realNatural-zero : realNatural zero ≡ 0ℝ
realNatural-zero = refl


realNatural-one : realNatural (suc zero) ≡ 1ℝ
realNatural-one = refl


realNatural-nonnegative : ∀ n →
  0ℝ ≤ℝ realNatural n
realNatural-nonnegative n =
  invEq (rat≤rat≃ (fromNat zero) (fromNat n))
    (0≤pos n (1+ zero))


realNatural-add : ∀ m n →
  realNatural (m ℕ.+ n) ≡
  realNatural m + realNatural n
realNatural-add m n =
  cong rat (sym (ℕ+→ℚ+ m n))
  ∙ sym (rat+rat (fromNat m) (fromNat n))


realNatural-mul : ∀ m n →
  realNatural (m ℕ.· n) ≡
  realNatural m · realNatural n
realNatural-mul m n =
  cong rat (sym (ℕ·→ℚ· m n))
  ∙ sym (mul-rat (fromNat m) (fromNat n))


realNatural-suc : ∀ n →
  realNatural (suc n) ≡ realNatural n + 1ℝ
realNatural-suc n =
  cong realNatural
    (sym (ℕ.+-suc n zero ∙ cong suc (ℕ.+-zero n)))
  ∙ realNatural-add n (suc zero)


realNatural-mono : ∀ {m n} →
  m ℕOrder.≤ n → realNatural m ≤ℝ realNatural n
realNatural-mono {m} {n} (difference , difference+m≡n) =
  subst2 _≤ℝ_
    (addIdL (realNatural m))
    (sym (realNatural-add difference m)
    ∙ cong realNatural difference+m≡n)
    (addPres≤R
      0ℝ (realNatural difference) (realNatural m)
      (realNatural-nonnegative difference))
