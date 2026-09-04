module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pythagorean where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as ℕOrder
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum using (inl)
open import Cubical.Data.Rationals.Base as ℚ using (fromNat)
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.Inverse.Signed
open import Cubical.Analysis.Real.Functions.Powers using (powℝ)
open import Cubical.Analysis.Real.Order.Apartness
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Rational using (<ℚ→<ℝ)
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Product.Finite
open import Cubical.Analysis.Real.Series.Product.Native
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant
open import Cubical.Analysis.Real.Series.PowerSeries.Operations
open import Cubical.Analysis.Real.Series.PowerSeries.Product
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Product.Derivative
open import
  Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import
  Cubical.Analysis.Real.Series.PowerSeries.Exponential.Archimedean
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Convergence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)


sineSquareCoefficients : RealSequence
sineSquareCoefficients =
  cauchyProduct sineCoefficients sineCoefficients


cosineSquareCoefficients : RealSequence
cosineSquareCoefficients =
  cauchyProduct cosineCoefficients cosineCoefficients


pythagoreanCoefficients : RealSequence
pythagoreanCoefficients n =
  sineSquareCoefficients n + cosineSquareCoefficients n


private
  cauchyProduct-negLeft : ∀ a b n →
    cauchyProduct (-_ ∘ a) b n ≡ - cauchyProduct a b n
  cauchyProduct-negLeft a b n =
    partialSum-pointwise
      (λ k → (- a k) · b (n ℕ.∸ k))
      (λ k → - (a k · b (n ℕ.∸ k)))
      (λ k → ℝRing.-DistL· (a k) (b (n ℕ.∸ k)))
      (suc n)
    ∙ partialSum-neg
        (λ k → a k · b (n ℕ.∸ k))
        (suc n)


  cauchyProduct-negRight : ∀ a b n →
    cauchyProduct a (-_ ∘ b) n ≡ - cauchyProduct a b n
  cauchyProduct-negRight a b n =
    partialSum-pointwise
      (λ k → a k · (- b (n ℕ.∸ k)))
      (λ k → - (a k · b (n ℕ.∸ k)))
      (λ k → ℝRing.-DistR· (a k) (b (n ℕ.∸ k)))
      (suc n)
    ∙ partialSum-neg
        (λ k → a k · b (n ℕ.∸ k))
        (suc n)


  sineSquareFormalDerivative : ∀ n →
    formalDerivative sineSquareCoefficients n ≡
    cauchyProduct sineCoefficients cosineCoefficients n
      + cauchyProduct sineCoefficients cosineCoefficients n
  sineSquareFormalDerivative n =
    formalDerivative-cauchyProduct-pointwise
      sineCoefficients sineCoefficients n
    ∙ cong₂ _+_
        (cong
          (λ a → cauchyProduct a sineCoefficients n)
          formalDerivative-sineCoefficients)
        (cong
          (λ b → cauchyProduct sineCoefficients b n)
          formalDerivative-sineCoefficients)
    ∙ cong
        (_+ cauchyProduct sineCoefficients cosineCoefficients n)
        (cauchyProduct-comm
          cosineCoefficients sineCoefficients n)


  cosineSquareFormalDerivative : ∀ n →
    formalDerivative cosineSquareCoefficients n ≡
    (- cauchyProduct sineCoefficients cosineCoefficients n)
      + (- cauchyProduct sineCoefficients cosineCoefficients n)
  cosineSquareFormalDerivative n =
    formalDerivative-cauchyProduct-pointwise
      cosineCoefficients cosineCoefficients n
    ∙ cong₂ _+_
        (cong
          (λ a → cauchyProduct a cosineCoefficients n)
          formalDerivative-cosineCoefficients)
        (cong
          (λ b → cauchyProduct cosineCoefficients b n)
          formalDerivative-cosineCoefficients)
    ∙ cong₂ _+_
        (cauchyProduct-negLeft
          sineCoefficients cosineCoefficients n)
        ( cauchyProduct-negRight
            cosineCoefficients sineCoefficients n
        ∙ cong -_
            (cauchyProduct-comm
              cosineCoefficients sineCoefficients n)
        )


formalDerivative-pythagoreanCoefficients-pointwise : ∀ n →
  formalDerivative pythagoreanCoefficients n ≡ 0ℝ
formalDerivative-pythagoreanCoefficients-pointwise n =
  funExt⁻ (formalDerivative-add
    sineSquareCoefficients cosineSquareCoefficients) n
  ∙ cong₂ _+_
      (sineSquareFormalDerivative n)
      (cosineSquareFormalDerivative n)
  ∙ cong
      (( cauchyProduct sineCoefficients cosineCoefficients n
        + cauchyProduct sineCoefficients cosineCoefficients n) +_)
      (sym
        (negAdd
          (cauchyProduct sineCoefficients cosineCoefficients n)
          (cauchyProduct sineCoefficients cosineCoefficients n)))
  ∙ addInvR
      (cauchyProduct sineCoefficients cosineCoefficients n
        + cauchyProduct sineCoefficients cosineCoefficients n)


formalDerivative-pythagoreanCoefficients :
  formalDerivative pythagoreanCoefficients ≡ (λ _ → 0ℝ)
formalDerivative-pythagoreanCoefficients =
  funExt formalDerivative-pythagoreanCoefficients-pointwise


pythagoreanCoefficients-zero :
  pythagoreanCoefficients zero ≡ 1ℝ
pythagoreanCoefficients-zero =
  cong₂ _+_
    ( cauchyProduct-zero sineCoefficients sineCoefficients
    ∙ cong₂ _·_ sineCoefficients-zero sineCoefficients-zero
    ∙ ℝRing.0LeftAnnihilates 0ℝ
    )
    ( cauchyProduct-zero cosineCoefficients cosineCoefficients
    ∙ cong₂ _·_ cosineCoefficients-zero cosineCoefficients-zero
    ∙ mulIdL 1ℝ
    )
  ∙ addIdL 1ℝ


private
  realNatural-suc-apart : ∀ n →
    0ℝ #ℝ realNatural (suc n)
  realNatural-suc-apart n =
    inl (<ℚ→<ℝ 0 (fromNat (suc n)) (ℚ.0<sucN n))


pythagoreanCoefficients-unit-pointwise : ∀ n →
  pythagoreanCoefficients n ≡ unitSeries n
pythagoreanCoefficients-unit-pointwise zero =
  pythagoreanCoefficients-zero
pythagoreanCoefficients-unit-pointwise (suc n) =
  mul-cancel-left-apart
    (pythagoreanCoefficients (suc n))
    0ℝ
    (realNatural (suc n))
    (realNatural-suc-apart n)
    ( formalDerivative-pythagoreanCoefficients-pointwise n
    ∙ sym (ℝRing.0RightAnnihilates (realNatural (suc n)))
    )


pythagoreanCoefficients-unit :
  pythagoreanCoefficients ≡ unitSeries
pythagoreanCoefficients-unit =
  funExt pythagoreanCoefficients-unit-pointwise


private
  powerSeriesIsAbsolutelyCauchyByExponentialMajorant :
    ∀ coefficients →
    CoefficientMajorizedBy coefficients exponentialCoefficients →
    ∀ x →
    IsAbsolutelyCauchySeries (powerSeriesTerms coefficients x)
  powerSeriesIsAbsolutelyCauchyByExponentialMajorant
      coefficients majorized x =
    dominatedCauchySeriesIsCauchy
      (absℝ ∘ powerSeriesTerms coefficients x)
      (powerSeriesTerms exponentialCoefficients (absℝ x))
      dominates
      (exponentialPowerSeriesIsCauchyEverywhere (absℝ x))
    where
    dominates : ∀ n →
      absℝ (absℝ (powerSeriesTerms coefficients x n)) ≤ℝ
      powerSeriesTerms exponentialCoefficients (absℝ x) n
    dominates n =
      subst
        (_≤ℝ powerSeriesTerms exponentialCoefficients (absℝ x) n)
        (sym (absIdem (powerSeriesTerms coefficients x n)))
        (powerSeriesTermAbsBoundByCoefficientMajorant
          coefficients exponentialCoefficients x (absℝ x)
          majorized (≤ℝ-refl (absℝ x)) n)


sinePowerSeriesIsAbsolutelyCauchy : ∀ x →
  IsAbsolutelyCauchySeries (powerSeriesTerms sineCoefficients x)
sinePowerSeriesIsAbsolutelyCauchy =
  powerSeriesIsAbsolutelyCauchyByExponentialMajorant
    sineCoefficients sineCoefficientsMajorizedByExponential


cosinePowerSeriesIsAbsolutelyCauchy : ∀ x →
  IsAbsolutelyCauchySeries (powerSeriesTerms cosineCoefficients x)
cosinePowerSeriesIsAbsolutelyCauchy =
  powerSeriesIsAbsolutelyCauchyByExponentialMajorant
    cosineCoefficients cosineCoefficientsMajorizedByExponential


sineSquareSeriesHasSum : ∀ x →
  HasSum
    (cauchyProduct
      (powerSeriesTerms sineCoefficients x)
      (powerSeriesTerms sineCoefficients x))
    (sinℝ x · sinℝ x)
sineSquareSeriesHasSum x =
  nativeMertensCauchyProductHasSum
    (powerSeriesTerms sineCoefficients x)
    (powerSeriesTerms sineCoefficients x)
    (sinℝ x) (sinℝ x)
    (sinePowerSeriesIsAbsolutelyCauchy x)
    (absoluteCauchySeriesIsCauchy
      (powerSeriesTerms sineCoefficients x)
      (sinePowerSeriesIsAbsolutelyCauchy x))
    (sinePowerSeriesHasSum x)
    (sinePowerSeriesHasSum x)


cosineSquareSeriesHasSum : ∀ x →
  HasSum
    (cauchyProduct
      (powerSeriesTerms cosineCoefficients x)
      (powerSeriesTerms cosineCoefficients x))
    (cosℝ x · cosℝ x)
cosineSquareSeriesHasSum x =
  nativeMertensCauchyProductHasSum
    (powerSeriesTerms cosineCoefficients x)
    (powerSeriesTerms cosineCoefficients x)
    (cosℝ x) (cosℝ x)
    (cosinePowerSeriesIsAbsolutelyCauchy x)
    (absoluteCauchySeriesIsCauchy
      (powerSeriesTerms cosineCoefficients x)
      (cosinePowerSeriesIsAbsolutelyCauchy x))
    (cosinePowerSeriesHasSum x)
    (cosinePowerSeriesHasSum x)


pythagoreanPowerSeriesTerms-product : ∀ x →
  powerSeriesTerms pythagoreanCoefficients x ≡
  (λ n →
    cauchyProduct
      (powerSeriesTerms sineCoefficients x)
      (powerSeriesTerms sineCoefficients x) n
    + cauchyProduct
      (powerSeriesTerms cosineCoefficients x)
      (powerSeriesTerms cosineCoefficients x) n)
pythagoreanPowerSeriesTerms-product x =
  funExt λ n →
    powerSeriesTerms-add
      sineSquareCoefficients cosineSquareCoefficients x n
    ∙ cong₂ _+_
        (powerSeriesTerms-cauchyProduct
          sineCoefficients sineCoefficients x n)
        (powerSeriesTerms-cauchyProduct
          cosineCoefficients cosineCoefficients x n)


private
  pythagoreanProductSeriesSummable : ∀ x →
    Summable
      (λ n →
        cauchyProduct
          (powerSeriesTerms sineCoefficients x)
          (powerSeriesTerms sineCoefficients x) n
        + cauchyProduct
          (powerSeriesTerms cosineCoefficients x)
          (powerSeriesTerms cosineCoefficients x) n)
  pythagoreanProductSeriesSummable x =
    addSummable
      (cauchyProduct
        (powerSeriesTerms sineCoefficients x)
        (powerSeriesTerms sineCoefficients x))
      (cauchyProduct
        (powerSeriesTerms cosineCoefficients x)
        (powerSeriesTerms cosineCoefficients x))
      (sinℝ x · sinℝ x , sineSquareSeriesHasSum x)
      (cosℝ x · cosℝ x , cosineSquareSeriesHasSum x)


pythagoreanPowerSeriesHasProductSum : ∀ x →
  HasSum
    (powerSeriesTerms pythagoreanCoefficients x)
    (sinℝ x · sinℝ x + cosℝ x · cosℝ x)
pythagoreanPowerSeriesHasProductSum x =
  subst
    (λ terms →
      HasSum terms
        (sinℝ x · sinℝ x + cosℝ x · cosℝ x))
    (sym (pythagoreanPowerSeriesTerms-product x))
    (seriesSumHasSum
      _ (pythagoreanProductSeriesSummable x))


private
  powerSeriesTerms-unitSeries : ∀ x →
    powerSeriesTerms unitSeries x ≡ unitSeries
  powerSeriesTerms-unitSeries x =
    funExt λ where
      zero → mulIdL 1ℝ
      (suc n) →
        ℝRing.0LeftAnnihilates (powℝ x (suc n))


  partialSum-unitSeries-positive : ∀ n →
    partialSum unitSeries (suc n) ≡ 1ℝ
  partialSum-unitSeries-positive zero =
    addIdL 1ℝ
  partialSum-unitSeries-positive (suc n) =
    cong (_+ 0ℝ) (partialSum-unitSeries-positive n)
    ∙ addIdR 1ℝ


  unitSeriesHasSum : HasSum unitSeries 1ℝ
  unitSeriesHasSum =
    eventuallyEqualPresIsLimitSequence
      ∣ 1 , (λ where
        zero one≤zero →
          ⊥.rec (ℕOrder.¬-<-zero one≤zero)
        (suc n) _ →
          sym (partialSum-unitSeries-positive n))
      ∣₁
      (constantIsLimitSequence 1ℝ)


  pythagoreanPowerSeriesTerms-unit : ∀ x →
    powerSeriesTerms pythagoreanCoefficients x ≡ unitSeries
  pythagoreanPowerSeriesTerms-unit x =
    cong
      (λ coefficients → powerSeriesTerms coefficients x)
      pythagoreanCoefficients-unit
    ∙ powerSeriesTerms-unitSeries x


  pythagoreanPowerSeriesHasOneSum : ∀ x →
    HasSum (powerSeriesTerms pythagoreanCoefficients x) 1ℝ
  pythagoreanPowerSeriesHasOneSum x =
    subst
      (λ terms → HasSum terms 1ℝ)
      (sym (pythagoreanPowerSeriesTerms-unit x))
      unitSeriesHasSum


opaque
  sin²+cos²≡1 : ∀ x →
    sinℝ x · sinℝ x + cosℝ x · cosℝ x ≡ 1ℝ
  sin²+cos²≡1 x =
    cong fst
      (isPropSequenceLimit
        (partialSum (powerSeriesTerms pythagoreanCoefficients x))
        ( (sinℝ x · sinℝ x + cosℝ x · cosℝ x)
        , pythagoreanPowerSeriesHasProductSum x
        )
        (1ℝ , pythagoreanPowerSeriesHasOneSum x))
