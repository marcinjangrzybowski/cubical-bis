module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Coefficients where

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Prelude
import Cubical.Data.Nat.Order as ℕ
import Cubical.Data.Int.Fast.Order as ℤ
import Cubical.Data.Rationals.Inverse as ℚInv
import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚAbs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue as Abs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base as Scalar
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul


arctangentDerivativeCoefficients : RealSequence
arctangentDerivativeCoefficients =
  alternatingEvenCoefficients unitCoefficients

arctangentCoefficients : RealSequence
arctangentCoefficients =
  formalPrimitive zeroℝ arctangentDerivativeCoefficients

formalDerivative-arctangentCoefficients :
  formalDerivative arctangentCoefficients
    ≡ arctangentDerivativeCoefficients
formalDerivative-arctangentCoefficients =
  formalDerivative-formalPrimitive zeroℝ arctangentDerivativeCoefficients


private
  squarePower≡evenPower : ∀ x n →
    (x Mul.· x) ^ⁿ n ≡ x ^ⁿ doubleℕ n
  squarePower≡evenPower x zero = refl
  squarePower≡evenPower x (suc n) =
      cong ((x Mul.· x) Mul.·_) (squarePower≡evenPower x n)
    ∙ sym (mul-assoc x x (x ^ⁿ doubleℕ n))

  arctangentDerivativeTerm-even : ∀ x k →
    powerSeriesTerms arctangentDerivativeCoefficients x (doubleℕ k)
      ≡ geometricTerms (Neg.- (x Mul.· x)) k
  arctangentDerivativeTerm-even x k =
      cong (Mul._· x ^ⁿ doubleℕ k)
        (alternatingEvenCoefficients-even unitCoefficients k)
    ∙ cong (ℝRing.alternate k oneℝ Mul.·_)
        (sym (squarePower≡evenPower x k))
    ∙ sym (alternate-mul-left k oneℝ ((x Mul.· x) ^ⁿ k))
    ∙ cong (ℝRing.alternate k)
        (mul-one-left ((x Mul.· x) ^ⁿ k))
    ∙ sym (negativePower k (x Mul.· x))

  arctangentDerivativeTerm-odd : ∀ x k →
    powerSeriesTerms arctangentDerivativeCoefficients x
        (suc (doubleℕ k)) ≡ zeroℝ
  arctangentDerivativeTerm-odd x k =
      cong (Mul._· x ^ⁿ suc (doubleℕ k))
        (alternatingEvenCoefficients-odd unitCoefficients k)
    ∙ mul-zero-left (x ^ⁿ suc (doubleℕ k))


opaque
  arctangentDerivativeTermsAsInterleavedGeometric : ∀ x →
    powerSeriesTerms arctangentDerivativeCoefficients x
      ≡ zeroInterleave (geometricTerms (Neg.- (x Mul.· x)))
  arctangentDerivativeTermsAsInterleavedGeometric x =
    funExt pointwise
    where
    pointwise : ∀ n →
      powerSeriesTerms arctangentDerivativeCoefficients x n
        ≡ zeroInterleave (geometricTerms (Neg.- (x Mul.· x))) n
    pointwise n with parity n
    ... | even k =
        arctangentDerivativeTerm-even x k
      ∙ sym (zeroInterleave-even
          (geometricTerms (Neg.- (x Mul.· x))) k)
    ... | odd k =
        arctangentDerivativeTerm-odd x k
      ∙ sym (zeroInterleave-odd
          (geometricTerms (Neg.- (x Mul.· x))) k)


arctangentCoefficient-zero :
  arctangentCoefficients zero ≡ zeroℝ
arctangentCoefficient-zero = refl


private
  one-nonnegative : zeroℝ ≤ℝ oneℝ
  one-nonnegative = ≤ℚ→≤ℝ 0 1 (ℚAbs.0≤pos 1 (1+ zero))


arctangentDerivativeCoefficientsBounded :
  CoefficientAbsBound onePositiveRational
    arctangentDerivativeCoefficients
arctangentDerivativeCoefficientsBounded =
  alternatingEvenCoefficients-majorized
    unitCoefficients (λ _ → one-nonnegative)


private
  one≤successorRational : ∀ n →
    ℚ.fromNat 1 ℚ.≤ ℚ.fromNat (suc n)
  one≤successorRational n =
    ≤ℤ→≤ℚ (pos 1) (pos (suc n))
      (ℤ.ℕ≤→pos-≤-pos 1 (suc n)
        (ℕ.suc-≤-suc ℕ.zero-≤))

  successorInverse≤one : ∀ n →
    fst ((successorPositiveRational n) ⁻¹₊) ℚ.≤ 1
  successorInverse≤one n =
    ℚInv.invℚ₊≤invℚ₊
      (successorPositiveRational n) onePositiveRational
      (one≤successorRational n)


opaque
  arctangentCoefficientsBounded :
    CoefficientAbsBound onePositiveRational arctangentCoefficients
  arctangentCoefficientsBounded zero =
    subst (_≤ℝ oneℝ) (sym Abs.absℝ-zero) one-nonnegative
  arctangentCoefficientsBounded (suc n) =
    ≤ℝ-trans
      (Abs.absℝ (arctangentCoefficients (suc n)))
      (inverse Scalar.⋆ oneℝ) oneℝ
      absolute≤scaled-one scaled-one≤one
    where
    inverse : ℚ
    inverse = fst ((successorPositiveRational n) ⁻¹₊)

    inverse-nonnegative : 0 ℚ.≤ inverse
    inverse-nonnegative =
      ℚ.<Weaken≤ 0 inverse (snd ((successorPositiveRational n) ⁻¹₊))

    absolute≤scaled-one :
      Abs.absℝ (arctangentCoefficients (suc n))
        ≤ℝ inverse Scalar.⋆ oneℝ
    absolute≤scaled-one =
      subst
        (λ left → left ≤ℝ inverse Scalar.⋆ oneℝ)
        (nonnegative-scalar-abs inverse inverse-nonnegative
          (arctangentDerivativeCoefficients n))
        (scalar-preserves≤ inverse inverse-nonnegative
          (Abs.absℝ (arctangentDerivativeCoefficients n)) oneℝ
          (arctangentDerivativeCoefficientsBounded n))

    scaled-one-path : inverse Scalar.⋆ oneℝ ≡ Real.ιℚ inverse
    scaled-one-path = Scalar.scalar-ι inverse 1 ∙ cong Real.ιℚ ℚ!

    scaled-one≤one : inverse Scalar.⋆ oneℝ ≤ℝ oneℝ
    scaled-one≤one =
      subst (_≤ℝ oneℝ) (sym scaled-one-path)
        (≤ℚ→≤ℝ inverse 1 (successorInverse≤one n))
