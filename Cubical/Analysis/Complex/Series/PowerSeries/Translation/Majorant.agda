module Cubical.Analysis.Complex.Series.PowerSeries.Translation.Majorant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; suc; _∸_)
import Cubical.Data.Nat as Nat
open import Cubical.Data.FinData using (toℕ)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Functions.Powers.Ring
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Bounds as Real
import Cubical.Analysis.Real.Series.Product.Finite as Real
import Cubical.Analysis.Real.FiniteSum.Reindexing as Real
import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.DividedPowers as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Coefficients
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Finite

import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Algebra as Algebra

private module A = Algebra.TranslationAlgebra ℝCommRing
private module RealSum = Sum (CommRing→Ring ℝCommRing)

-- The positive binomial double series controlling the translated rows.
-- Its anti-diagonals are exactly the original norm-majorant at |center|+r.
translatedCoefficientMajorant : ComplexSequence → ℂ → ℕ → Real.RealSequence
translatedCoefficientMajorant coefficients center order index =
  (realNatural (Nat._choose_ (index Nat.+ order) order) · normℂ (coefficients (index Nat.+ order)))
    · powℝ (normℂ center) index

opaque
  translatedCoefficientTermNormBound : ∀ coefficients center order index →
    normℂ (translatedCoefficientTermsℂ coefficients center order index)
      ≤ℝ translatedCoefficientMajorant coefficients center order index
  translatedCoefficientTermNormBound coefficients center order index =
    normℂ-mulBound (binomialCoefficientℂ total order ·ℂ coefficients total) (center ^ℂ index)
      (realNatural (Nat._choose_ total order) · normℂ (coefficients total))
      (powℝ (normℂ center) index)
      (normℂ-mulBound (binomialCoefficientℂ total order) (coefficients total)
        (realNatural (Nat._choose_ total order)) (normℂ (coefficients total))
        (subst (_≤ℝ realNatural (Nat._choose_ total order)) (sym binomialNorm)
          (≤ℝ-refl (realNatural (Nat._choose_ total order))))
        (≤ℝ-refl (normℂ (coefficients total))))
      (complexPowerNormBound center index)
    where
    total : ℕ
    total = index Nat.+ order

    binomialNorm : normℂ (binomialCoefficientℂ total order) ≡ realNatural (Nat._choose_ total order)
    binomialNorm = normℂ-fromℝ (realNatural (Nat._choose_ total order))
      ∙ absOfNonnegative (realNatural (Nat._choose_ total order))
          (realNatural-nonnegative (Nat._choose_ total order))

  translatedCoefficientMajorantNonnegative : ∀ coefficients center order index →
    0ℝ ≤ℝ translatedCoefficientMajorant coefficients center order index
  translatedCoefficientMajorantNonnegative coefficients center order index =
    ≤ℝ-trans 0ℝ (normℂ (translatedCoefficientTermsℂ coefficients center order index))
      (translatedCoefficientMajorant coefficients center order index)
      (normℂ-nonnegative (translatedCoefficientTermsℂ coefficients center order index))
      (translatedCoefficientTermNormBound coefficients center order index)

opaque
  translatedMajorantDiagonal : ∀ coefficients center radius n →
    Real.diagonalSum (λ order index → translatedCoefficientMajorant coefficients center order index · powℝ radius order) n
      ≡ complexPowerSeriesMajorant coefficients (normℂ center + radius) n
  translatedMajorantDiagonal coefficients center radius n =
    Real.partialSum-as-finSum
      (λ order → translatedCoefficientMajorant coefficients center order (n ∸ order) · powℝ radius order) (suc n)
    ∙ RealSum.∑Ext {n = suc n} (λ k → cong₂ _·_
        (cong ((realNatural (Nat._choose_ ((n ∸ toℕ k) Nat.+ toℕ k) (toℕ k))
          · normℂ (coefficients ((n ∸ toℕ k) Nat.+ toℕ k))) ·_)
          (powℝ-as-ringPower (normℂ center) (n ∸ toℕ k)))
        (powℝ-as-ringPower radius (toℕ k)))
    ∙ A.translatedMonomialAddition (normℂ ∘ coefficients) (λ total order → realNatural (Nat._choose_ total order))
        (λ total order → sym (Real.realBinomialCoefficient-agreesNatural total order)) (normℂ center) radius n
    ∙ cong (normℂ (coefficients n) ·_) (sym (powℝ-as-ringPower (normℂ center + radius) n))

opaque
  finiteTranslatedMajorantBound : ∀ coefficients center radius → 0ℝ ≤ℝ radius → ∀ count →
    Real.partialSum (complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius) count
      ≤ℝ Real.partialSum (complexPowerSeriesMajorant coefficients (normℂ center + radius)) count
  finiteTranslatedMajorantBound coefficients center radius positive count =
    subst (Real.partialSum (complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius) count ≤ℝ_)
      reindex
      (Real.partialSumMono
        (complexPowerSeriesMajorant (finiteTranslatedCoefficientsℂ coefficients center count) radius)
        (λ order → Real.partialSum (translatedCoefficientMajorant coefficients center order) (count ∸ order) · powℝ radius order)
        (λ order → mulPres≤R-0≤
          (normℂ (finiteTranslatedCoefficientsℂ coefficients center count order))
          (Real.partialSum (translatedCoefficientMajorant coefficients center order) (count ∸ order))
          (powℝ radius order) (powNonnegative radius order positive)
          (partialSumℂBoundBy (translatedCoefficientTermsℂ coefficients center order)
            (translatedCoefficientMajorant coefficients center order)
            (translatedCoefficientTermNormBound coefficients center order) (count ∸ order))) count)
    where
    weighted : ℕ → ℕ → ℝ
    weighted order index = translatedCoefficientMajorant coefficients center order index · powℝ radius order

    reindex : Real.partialSum
      (λ order → Real.partialSum (translatedCoefficientMajorant coefficients center order) (count ∸ order) · powℝ radius order) count
      ≡ Real.partialSum (complexPowerSeriesMajorant coefficients (normℂ center + radius)) count
    reindex = Real.partialSum-pointwise
      (λ order → Real.partialSum (translatedCoefficientMajorant coefficients center order) (count ∸ order) · powℝ radius order)
      (λ order → Real.partialSum (weighted order) (count ∸ order))
      (λ order → sym (Real.partialSum-right-scale (translatedCoefficientMajorant coefficients center order) (powℝ radius order) (count ∸ order))) count
      ∙ sym (Real.partialSum-diagonalSum weighted count)
      ∙ Real.partialSum-pointwise (Real.diagonalSum weighted)
          (complexPowerSeriesMajorant coefficients (normℂ center + radius))
          (translatedMajorantDiagonal coefficients center radius) count
