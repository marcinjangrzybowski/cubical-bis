module Cubical.Analysis.Complex.Series.PowerSeries.Difference.Sum where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat as ℕ using (zero; suc)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Operations
open import Cubical.Analysis.Complex.Series.Tails
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference

-- These identities need only supplied sums. The convergence construction
-- and its stronger native Cauchy hypotheses are kept separate.
opaque
  powerSeriesDifferenceFactorℂDiagonalValue : ∀ coefficients x factor derivative →
    HasComplexSum (powerSeriesDifferenceFactorℂ coefficients x x) factor →
    HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) x) derivative → factor ≡ derivative
  powerSeriesDifferenceFactorℂDiagonalValue coefficients x factor derivative fs ds =
    complexSumUnique (powerSeriesTermsℂ (formalDerivativeℂ coefficients) x) factor derivative
      (complexHasSumPointwise (powerSeriesDifferenceFactorℂ coefficients x x)
        (powerSeriesTermsℂ (formalDerivativeℂ coefficients) x)
        (powerSeriesDifferenceFactorℂ-diagonal coefficients x) factor fs) ds

opaque
  powerSeriesValueℂDifferenceFactorization : ∀ coefficients x y fx fy factor →
    HasComplexSum (powerSeriesTermsℂ coefficients x) fx →
    HasComplexSum (powerSeriesTermsℂ coefficients y) fy →
    HasComplexSum (powerSeriesDifferenceFactorℂ coefficients x y) factor →
    fy -ℂ fx ≡ (y -ℂ x) ·ℂ factor
  powerSeriesValueℂDifferenceFactorization coefficients x y fx fy factor xs ys fs =
    complexSumUnique scaled (fy -ℂ fx) ((y -ℂ x) ·ℂ factor)
      (complexHasSumPointwise tail scaled equal (fy -ℂ fx) tailSum)
      (scaleHasComplexSum (y -ℂ x) factors factor fs)
    where
    difference factors tail scaled : ComplexSequence
    difference n = powerSeriesTermsℂ coefficients y n -ℂ powerSeriesTermsℂ coefficients x n
    factors = powerSeriesDifferenceFactorℂ coefficients x y
    tail = dropComplexSeries (suc zero) difference
    scaled = scaleComplexSeries (y -ℂ x) factors

    prefixZero : partialSumℂ difference (suc zero) ≡ 0ℂ
    prefixZero = +ℂComm 0ℂ (difference zero) ∙ +ℂIdR (difference zero)
      ∙ cong₂ _-ℂ_ (powerSeriesTermsℂ-zero coefficients y) (powerSeriesTermsℂ-zero coefficients x)
      ∙ +ℂInvR (coefficients zero)

    tailSum : HasComplexSum tail (fy -ℂ fx)
    tailSum = subst (HasComplexSum tail)
      (cong (λ z → (fy -ℂ fx) -ℂ z) prefixZero
        ∙ cong ((fy -ℂ fx) +ℂ_) ℂRing.0Selfinverse ∙ +ℂIdR (fy -ℂ fx))
      (dropComplexSeriesHasSum (suc zero) difference (fy -ℂ fx)
        (subHasComplexSum (powerSeriesTermsℂ coefficients y) (powerSeriesTermsℂ coefficients x) fy fx ys xs))

    equal : ∀ n → tail n ≡ scaled n
    equal n = cong difference (ℕ.+-suc n zero ∙ cong suc (ℕ.+-zero n))
      ∙ powerSeriesDifferenceFactorℂ-identity coefficients x y n
