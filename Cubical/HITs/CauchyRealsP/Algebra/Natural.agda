module Cubical.HITs.CauchyRealsP.Algebra.Natural where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
  using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as ℕOrder
open import Cubical.Data.NatPlusOne
  using (one)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Order
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication

realNatural : ℕ → ℝ
realNatural zero =
  0
realNatural (suc n) =
  realNatural n + 1

realNatural-add :
  ∀ m n →
  realNatural (m ℕ.+ n)
    ≡
  realNatural m + realNatural n
realNatural-add zero n =
  sym (addIdL (realNatural n))
realNatural-add (suc m) n =
  cong (_+ 1)
    (realNatural-add m n)
  ∙ sym
      (addAssoc
        (realNatural m)
        (realNatural n)
        1)
  ∙ cong (realNatural m +_)
      (addComm (realNatural n) 1)
  ∙ addAssoc
      (realNatural m)
      1
      (realNatural n)

realNatural-mul :
  ∀ m n →
  realNatural (m ℕ.· n)
    ≡
  realNatural m · realNatural n
realNatural-mul zero n =
  sym (mulZeroL (realNatural n))
realNatural-mul (suc m) n =
  realNatural-add n (m ℕ.· n)
  ∙ cong (realNatural n +_)
      (realNatural-mul m n)
  ∙ addComm
      (realNatural n)
      (realNatural m · realNatural n)
  ∙ cong
      (realNatural m · realNatural n +_)
      (sym (mulIdL (realNatural n)))
  ∙ sym
      (mulDistL
        (realNatural m)
        1
        (realNatural n))

realNatural-rat :
  ∀ n →
  realNatural n
    ≡
  rat (ℚ.fromNat n)
realNatural-rat zero =
  refl
realNatural-rat (suc n) =
  cong (_+ 1)
    (realNatural-rat n)
  ∙ rat+rat
      (ℚ.fromNat n)
      1
  ∙ cong rat
      (ℚ.+Comm
        (ℚ.fromNat n) 1
      ∙ ℚ.ℕ+→ℚ+ 1 n)

realNatural-nonnegative :
  ∀ n →
  0 ≤ℝ realNatural n
realNatural-nonnegative zero =
  ≤ℝ-refl 0
realNatural-nonnegative (suc n) =
  subst2 _≤ℝ_
    (addIdL 0)
    refl
    (≤ℝ-add
      0 (realNatural n)
      0 1
      (realNatural-nonnegative n)
      (<ℝ-weaken
        0 1
        (<ℚ→<ℝ
          0 1
          (ℚ.0<pos 0 one))))

realNatural-mono :
  ∀ {m n} →
  m ℕOrder.≤ n →
  realNatural m ≤ℝ realNatural n
realNatural-mono
  {m} {n} (difference , difference+m≡n) =
    subst2 _≤ℝ_
      (addIdL (realNatural m))
      (sym
          (realNatural-add
            difference m)
        ∙ cong realNatural
            difference+m≡n)
      (≤ℝ-addR
        0
        (realNatural difference)
        (realNatural m)
        (realNatural-nonnegative
          difference))
