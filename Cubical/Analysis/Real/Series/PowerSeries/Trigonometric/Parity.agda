module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Parity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (negZero)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using
  (1ℝ; mulAssoc; mulComm; mulIdL; mulIdR)
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Operations
open import Cubical.Analysis.Real.Series.PowerSeries.Rescaling
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)

  reorderThreeFactors : ∀ x y z →
    (x · y) · z ≡ (x · z) · y
  reorderThreeFactors x y z =
    sym (mulAssoc x y z)
    ∙ cong (x ·_) (mulComm y z)
    ∙ mulAssoc x z y


mutual
  sineRationalSign-negOnePow : ∀ n →
    rat (sineRationalSign n) · powℝ (- 1ℝ) n
      ≡ - rat (sineRationalSign n)
  sineRationalSign-negOnePow zero =
    ℝRing.0LeftAnnihilates 1ℝ
    ∙ sym negZero
  sineRationalSign-negOnePow (suc n) =
    mulAssoc
      (rat (cosineRationalSign n)) (- 1ℝ) (powℝ (- 1ℝ) n)
    ∙ cong (_· powℝ (- 1ℝ) n)
        ( mulComm (rat (cosineRationalSign n)) (- 1ℝ)
        ∙ ℝRing.-DistL· 1ℝ (rat (cosineRationalSign n))
        ∙ cong -_ (mulIdL (rat (cosineRationalSign n)))
        )
    ∙ ℝRing.-DistL·
        (rat (cosineRationalSign n)) (powℝ (- 1ℝ) n)
    ∙ cong -_ (cosineRationalSign-negOnePow n)

  cosineRationalSign-negOnePow : ∀ n →
    rat (cosineRationalSign n) · powℝ (- 1ℝ) n
      ≡ rat (cosineRationalSign n)
  cosineRationalSign-negOnePow zero =
    mulIdL 1ℝ
  cosineRationalSign-negOnePow (suc n) =
    cong (_· ((- 1ℝ) · powℝ (- 1ℝ) n))
      (sym (neg-rat (sineRationalSign n)))
    ∙ mulAssoc (- rat (sineRationalSign n)) (- 1ℝ)
        (powℝ (- 1ℝ) n)
    ∙ cong (_· powℝ (- 1ℝ) n)
        (ℝRing.-Dist· (rat (sineRationalSign n)) 1ℝ
          ∙ mulIdR (rat (sineRationalSign n)))
    ∙ sineRationalSign-negOnePow n
    ∙ neg-rat (sineRationalSign n)


sineCoefficients-negOne-rescale-pointwise : ∀ n →
  rescaleCoefficients (- 1ℝ) sineCoefficients n
    ≡ - sineCoefficients n
sineCoefficients-negOne-rescale-pointwise n =
  cong (_· powℝ (- 1ℝ) n)
    (sym (mul-rat
      (sineRationalSign n)
      (exponentialRationalCoefficient n)))
  ∙ reorderThreeFactors
      (rat (sineRationalSign n))
      (rat (exponentialRationalCoefficient n))
      (powℝ (- 1ℝ) n)
  ∙ cong (_· rat (exponentialRationalCoefficient n))
      (sineRationalSign-negOnePow n)
  ∙ ℝRing.-DistL·
      (rat (sineRationalSign n))
      (rat (exponentialRationalCoefficient n))
  ∙ cong -_
      (mul-rat
        (sineRationalSign n)
        (exponentialRationalCoefficient n))


cosineCoefficients-negOne-rescale-pointwise : ∀ n →
  rescaleCoefficients (- 1ℝ) cosineCoefficients n
    ≡ cosineCoefficients n
cosineCoefficients-negOne-rescale-pointwise n =
  cong (_· powℝ (- 1ℝ) n)
    (sym (mul-rat
      (cosineRationalSign n)
      (exponentialRationalCoefficient n)))
  ∙ reorderThreeFactors
      (rat (cosineRationalSign n))
      (rat (exponentialRationalCoefficient n))
      (powℝ (- 1ℝ) n)
  ∙ cong (_· rat (exponentialRationalCoefficient n))
      (cosineRationalSign-negOnePow n)
  ∙ mul-rat
      (cosineRationalSign n)
      (exponentialRationalCoefficient n)


sineCoefficients-negOne-rescale :
  rescaleCoefficients (- 1ℝ) sineCoefficients
    ≡ (-_ ∘ sineCoefficients)
sineCoefficients-negOne-rescale =
  funExt sineCoefficients-negOne-rescale-pointwise


cosineCoefficients-negOne-rescale :
  rescaleCoefficients (- 1ℝ) cosineCoefficients
    ≡ cosineCoefficients
cosineCoefficients-negOne-rescale =
  funExt cosineCoefficients-negOne-rescale-pointwise


sinePowerSeriesTerms-negOne : ∀ x →
  powerSeriesTerms sineCoefficients ((- 1ℝ) · x)
    ≡ (-_ ∘ powerSeriesTerms sineCoefficients x)
sinePowerSeriesTerms-negOne x =
  sym
    (powerSeriesTerms-rescale-sequence
      (- 1ℝ) sineCoefficients x)
  ∙ cong (λ coefficients → powerSeriesTerms coefficients x)
      sineCoefficients-negOne-rescale
  ∙ powerSeriesTerms-neg-path sineCoefficients x


cosinePowerSeriesTerms-negOne : ∀ x →
  powerSeriesTerms cosineCoefficients ((- 1ℝ) · x)
    ≡ powerSeriesTerms cosineCoefficients x
cosinePowerSeriesTerms-negOne x =
  sym
    (powerSeriesTerms-rescale-sequence
      (- 1ℝ) cosineCoefficients x)
  ∙ cong (λ coefficients → powerSeriesTerms coefficients x)
      cosineCoefficients-negOne-rescale
