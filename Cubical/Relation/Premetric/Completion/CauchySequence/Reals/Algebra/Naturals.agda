module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc ; _+_ ; _·_)
import Cubical.Data.Nat.Order as ℕOrder
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals.Base as ℚ using (ℚ ; fromNatℚ)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚAbs
  using (0≤pos)

open import Cubical.Algebra.CommRing

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing


realNatural : ℕ → Real.ℝ
realNatural n = Real.ιℚ (ℚ.fromNat n)


realNatural-zero :
  realNatural zero ≡ CommRingStr.0r (snd ℝCommRing)
realNatural-zero = refl


realNatural-one :
  realNatural (suc zero) ≡ CommRingStr.1r (snd ℝCommRing)
realNatural-one = refl


realNatural-nonnegative : ∀ n →
  Real.ιℚ (ℚ.fromNat 0) ≤ℝ realNatural n
realNatural-nonnegative n =
  ≤ℚ→≤ℝ (ℚ.fromNat 0) (ℚ.fromNat n) (0≤pos n (1+ zero))


realNatural-add : ∀ m n →
  realNatural (m ℕ.+ n) ≡
  realNatural m Add.+ realNatural n
realNatural-add m n =
  cong Real.ιℚ (sym (ℚAbs.ℕ+→ℚ+ m n))
  ∙ sym (Add.add-ι-ι (ℚ.fromNat m) (ℚ.fromNat n))


realNatural-mul : ∀ m n →
  realNatural (m ℕ.· n) ≡
  realNatural m Mul.· realNatural n
realNatural-mul m n =
  cong Real.ιℚ (sym (ℚAbs.ℕ·→ℚ· m n))
  ∙ sym (Mul.mul-ι-ι (ℚ.fromNat m) (ℚ.fromNat n))


realNatural-suc : ∀ n →
  realNatural (suc n) ≡
  realNatural n Add.+ realNatural (suc zero)
realNatural-suc n =
  cong realNatural
    (sym (ℕ.+-suc n zero ∙ cong suc (ℕ.+-zero n)))
  ∙ realNatural-add n (suc zero)


realNatural-mono : ∀ {m n} →
  m ℕOrder.≤ n →
  realNatural m ≤ℝ realNatural n
realNatural-mono {m} {n} (difference , difference+m≡n) =
  subst2 _≤ℝ_
    (add-zero-left (realNatural m))
    (sym (realNatural-add difference m)
    ∙ cong realNatural difference+m≡n)
    (add-preserves≤-right
      (realNatural zero) (realNatural difference) (realNatural m)
      (realNatural-nonnegative difference))
