module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (suc)

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (abs-mul ; nonnegative→abs-self ; mul-nonnegative ; mul-monotone-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Majorant


formalDerivative : RealSequence → RealSequence
formalDerivative coefficients n =
  realNatural (suc n) Mul.· coefficients (suc n)


formalDerivative-add : ∀ a b →
  formalDerivative (λ n → a n Add.+ b n) ≡
  (λ n → formalDerivative a n Add.+ formalDerivative b n)
formalDerivative-add a b =
  funExt λ n →
    mul-distrib-over-add-right
      (realNatural (suc n)) (a (suc n)) (b (suc n))


formalDerivative-scale : ∀ c coefficients →
  formalDerivative (scaleSeries c coefficients) ≡
  scaleSeries c (formalDerivative coefficients)
formalDerivative-scale c coefficients =
  funExt λ n →
    mul-assoc
      (realNatural (suc n)) c (coefficients (suc n))
    ∙ cong (Mul._· coefficients (suc n))
        (mul-comm (realNatural (suc n)) c)
    ∙ sym (mul-assoc c (realNatural (suc n)) (coefficients (suc n)))


formalDerivative-zero :
  formalDerivative (λ _ → zeroℝ) ≡ (λ _ → zeroℝ)
formalDerivative-zero =
  funExt λ n → mul-zero-right (realNatural (suc n))


powerSeriesTerms-formalDerivative : ∀ coefficients x n →
  powerSeriesTerms (formalDerivative coefficients) x n ≡
  realNatural (suc n) Mul.·
    (coefficients (suc n) Mul.· x ^ⁿ n)
powerSeriesTerms-formalDerivative coefficients x n =
  sym (mul-assoc (realNatural (suc n))
    (coefficients (suc n)) (x ^ⁿ n))


formalDerivativeMajorant : RealSequence → RealSequence
formalDerivativeMajorant majorant n =
  realNatural (suc n) Mul.· majorant (suc n)


formalDerivativeMajorant-nonnegative : ∀ majorant →
  NonnegativeCoefficients majorant →
  NonnegativeCoefficients (formalDerivativeMajorant majorant)
formalDerivativeMajorant-nonnegative majorant nonnegative n =
  mul-nonnegative
    (realNatural (suc n)) (majorant (suc n))
    (realNatural-nonnegative (suc n))
    (nonnegative (suc n))


formalDerivativePresCoefficientMajorant : ∀ coefficients majorant →
  CoefficientMajorizedBy coefficients majorant →
  CoefficientMajorizedBy
    (formalDerivative coefficients)
    (formalDerivativeMajorant majorant)
formalDerivativePresCoefficientMajorant
  coefficients majorant majorized n =
  subst (_≤ℝ formalDerivativeMajorant majorant n)
    (sym absolutePath) productBound
  where
  absolutePath :
    Abs.absℝ (formalDerivative coefficients n) ≡
    realNatural (suc n) Mul.· Abs.absℝ (coefficients (suc n))
  absolutePath =
    abs-mul (realNatural (suc n)) (coefficients (suc n))
    ∙ cong (Mul._· Abs.absℝ (coefficients (suc n)))
        (nonnegative→abs-self
          (realNatural (suc n))
          (realNatural-nonnegative (suc n)))

  productBound :
    realNatural (suc n) Mul.· Abs.absℝ (coefficients (suc n)) ≤ℝ
    formalDerivativeMajorant majorant n
  productBound =
    mul-monotone-nonnegative
      (realNatural (suc n)) (realNatural (suc n))
      (Abs.absℝ (coefficients (suc n))) (majorant (suc n))
      (≤ℝ-refl (realNatural (suc n)))
      (majorized (suc n))
      (realNatural-nonnegative (suc n))
      (zero≤abs (coefficients (suc n)))
