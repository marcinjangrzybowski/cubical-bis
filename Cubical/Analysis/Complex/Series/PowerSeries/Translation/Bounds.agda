module Cubical.Analysis.Complex.Series.PowerSeries.Translation.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
import Cubical.Data.Nat.Order as Nat
import Cubical.Data.Sum as Sum
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as Ring
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Bounds as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Finite
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Majorant
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.RadiusBound public

private
  module R = Ring.RingTheory (CommRing→Ring ℝCommRing)
  majorantNonnegative : ∀ coefficients radius → 0ℝ ≤ℝ radius → ∀ n →
    0ℝ ≤ℝ complexPowerSeriesMajorant coefficients radius n
  majorantNonnegative coefficients radius positive n = isNonnegative→0≤
    (complexPowerSeriesMajorant coefficients radius n)
    (mulPresIsNonnegative (normℂ (coefficients n)) (powℝ radius n)
      (0≤→isNonnegative (normℂ (coefficients n)) (normℂ-nonnegative (coefficients n)))
      (powPresIsNonnegative radius n (0≤→isNonnegative radius positive)))

  termBelowPartialSum : ∀ terms → (∀ n → 0ℝ ≤ℝ terms n) → ∀ count index → index Nat.< count →
    terms index ≤ℝ Real.partialSum terms count
  termBelowPartialSum terms nonnegative count index below = ≤ℝ-trans
    (terms index) (Real.partialSum terms (suc index)) (Real.partialSum terms count)
    (subst (_≤ℝ Real.partialSum terms (suc index)) (addIdL (terms index))
      (addPres≤R 0ℝ (Real.partialSum terms index) (terms index)
        (Real.partialSumNonnegative terms nonnegative index)))
    (Real.partialSumIndexMono terms nonnegative (suc index) count below)

opaque
  -- Every coefficient of every translated finite polynomial has the same
  -- weighted bound. Coefficients beyond its degree are definitionally zero
  -- after the natural-number subtraction is simplified.
  finiteTranslatedCoefficientBound : ∀ (coefficients : ComplexSequence) (center : ℂ) (radius outer bound : ℝ) →
    0ℝ ≤ℝ radius → normℂ center + radius ≤ℝ outer →
    (∀ count → Real.partialSum (complexPowerSeriesMajorant coefficients outer) count ≤ℝ bound) →
    ∀ count order → complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius order ≤ℝ bound
  finiteTranslatedCoefficientBound coefficients center radius outer bound positive fits bounded count order =
    Sum.rec before after (Nat.splitℕ-< order count)
    where
    before : order Nat.< count →
      complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius order ≤ℝ bound
    before below = ≤ℝ-trans
      (complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius order)
      (Real.partialSum (complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius) count) bound
      (termBelowPartialSum (complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius)
        (majorantNonnegative (finiteTranslatedCoefficientsℂ coefficients center count) radius positive) count order below)
      (≤ℝ-trans
        (Real.partialSum (complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius) count)
        (Real.partialSum (complexPowerSeriesMajorant coefficients outer) count) bound
        (finiteTranslatedMajorantBoundOn coefficients center radius outer positive fits count) (bounded count))

    after : count Nat.≤ order →
      complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius order ≤ℝ bound
    after above = subst (_≤ℝ bound) (sym zeroTerm) (bounded 0)
      where
      zeroTerm : complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius order ≡ 0ℝ
      zeroTerm = cong (λ n → normℂ (partialSumℂ
          (translatedCoefficientTermsℂ coefficients center order) n)
          · powℝ radius order) (Nat.n∸m≡0 count order above)
        ∙ cong (_· powℝ radius order) normℂ-zero
        ∙ R.0LeftAnnihilates (powℝ radius order)
