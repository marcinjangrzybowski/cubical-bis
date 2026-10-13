module Cubical.Analysis.Real.Series.PowerSeries.InteriorConvergence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat as ℕ using (suc)
open import Cubical.Data.Rationals.Inverse using (_⁻¹₊)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.Tails
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.InteriorBound

private
  opaque
    commuteProduct : ∀ a b c → a · (b · c) ≡ b · (a · c)
    commuteProduct a b c = mulAssoc a b c
      ∙ cong (_· c) (mulComm a b) ∙ sym (mulAssoc b a c)

    successorSeriesIsCauchy : ∀ terms → IsCauchySeries terms →
      IsCauchySeries (λ n → terms (suc n))
    successorSeriesIsCauchy terms witness = subst IsCauchySeries
      (funExt λ n → cong terms (ℕ.+-comm n 1)) (dropSeriesIsCauchy 1 terms witness)

-- The outer witness belongs to the ORIGINAL nonnegative majorant. A single
-- truncated positive gap is eliminated into the proposition IsCauchySeries;
-- no family of independently chosen radii or moduli is required.
opaque
  formalDerivativeMajorantIsCauchyAtInterior : ∀ coefficients inner outer →
    NonnegativeCoefficients coefficients → 0ℝ ≤ℝ inner → inner <ℝ outer →
    IsCauchySeries (powerSeriesTerms coefficients outer) →
    IsCauchySeries (powerSeriesTerms (formalDerivativeMajorant coefficients) inner)
  formalDerivativeMajorantIsCauchyAtInterior coefficients inner outer nonnegative positive strict witness =
    PT.rec (isPropIsCauchySeries derivativeTerms) fromGap (positiveSub inner outer strict)
    where
    derivativeTerms : RealSequence
    derivativeTerms = powerSeriesTerms (formalDerivativeMajorant coefficients) inner

    outerTail : RealSequence
    outerTail n = powerSeriesTerms coefficients outer (suc n)

    ordered : inner ≤ℝ outer
    ordered = <ℝ-weaken inner outer strict

    derivativeNonnegative : ∀ n → 0ℝ ≤ℝ derivativeTerms n
    derivativeNonnegative n = isNonnegative→0≤ (derivativeTerms n)
      (mulPresIsNonnegative (formalDerivativeMajorant coefficients n) (powℝ inner n)
        (0≤→isNonnegative (formalDerivativeMajorant coefficients n)
          (formalDerivativeMajorant-nonnegative coefficients nonnegative n))
        (powPresIsNonnegative inner n (0≤→isNonnegative inner positive)))

    fromGap : PositiveGap 0ℝ (outer - inner) → IsCauchySeries derivativeTerms
    fromGap (gap , lower) = dominatedCauchySeriesIsCauchy derivativeTerms
      (scaleSeries (rat (fst (gap ⁻¹₊))) outerTail) dominates
      (rationalScaleSeriesIsCauchy (fst (gap ⁻¹₊)) outerTail
        (successorSeriesIsCauchy (powerSeriesTerms coefficients outer) witness))
      where
      dominates : ∀ n → absℝ (derivativeTerms n) ≤ℝ rat (fst (gap ⁻¹₊)) · outerTail n
      dominates n = subst2 _≤ℝ_ leftPath rightPath
        (mulPres≤L (realNatural (suc n) · powℝ inner n)
          (rat (fst (gap ⁻¹₊)) · powℝ outer (suc n))
          (coefficients (suc n)) (0≤→isNonnegative (coefficients (suc n)) (nonnegative (suc n)))
          (powerDerivativeBoundByOuterRadius inner outer gap positive ordered
            (subst (_≤ℝ outer - inner) (addIdL (rat (fst gap))) lower) n))
        where
        leftPath : coefficients (suc n) · (realNatural (suc n) · powℝ inner n) ≡ absℝ (derivativeTerms n)
        leftPath = commuteProduct (coefficients (suc n)) (realNatural (suc n)) (powℝ inner n)
          ∙ mulAssoc (realNatural (suc n)) (coefficients (suc n)) (powℝ inner n)
          ∙ sym (absOfNonnegative (derivativeTerms n) (derivativeNonnegative n))

        rightPath : coefficients (suc n) · (rat (fst (gap ⁻¹₊)) · powℝ outer (suc n))
          ≡ rat (fst (gap ⁻¹₊)) · outerTail n
        rightPath = commuteProduct (coefficients (suc n)) (rat (fst (gap ⁻¹₊))) (powℝ outer (suc n))
