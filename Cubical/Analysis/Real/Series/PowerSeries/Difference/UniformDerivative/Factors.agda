module Cubical.Analysis.Real.Series.PowerSeries.Difference.UniformDerivative.Factors where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Difference
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.UniformDerivative.Continuity
open import Cubical.Analysis.Real.Integration.UniformContinuity

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

private
  module Pℝ = PremetricStr (ℝPremetricSpace .snd)

  quarterHalfQuarter : ∀ ε →
    fst ((ε /4₊) +₊ ((ε /2₊) +₊ (ε /4₊))) ≡ fst ε
  quarterHalfQuarter ε =
    ℚ.+Assoc (fst (ε /4₊)) (fst (ε /2₊)) (fst (ε /4₊))
    ∙ cong (ℚ._+ fst (ε /4₊)) (ℚ.+Comm (fst (ε /4₊)) (fst (ε /2₊)))
    ∙ sym (ℚ.+Assoc (fst (ε /2₊)) (fst (ε /4₊)) (fst (ε /4₊)))
    ∙ cong (fst (ε /2₊) ℚ.+_) (/4+/4≡/2 (fst ε))
    ∙ /2+/2≡id (fst ε)


partialSumFamilyIsRadiuswiseUniformlyContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
    (terms : A → RealSequence) →
  (∀ n → IsRadiuswiseUniformlyContinuous source
    (λ point → terms point n) (ℝPremetricSpace .snd)) →
  ∀ n → IsRadiuswiseUniformlyContinuous source
    (λ point → partialSum (terms point) n) (ℝPremetricSpace .snd)
partialSumFamilyIsRadiuswiseUniformlyContinuous source terms term-uc zero =
  constantIsRadiuswiseUniformlyContinuous source 0ℝ
partialSumFamilyIsRadiuswiseUniformlyContinuous source terms term-uc (suc n) =
  sumIsRadiuswiseUniformlyContinuous source
    (λ point → partialSum (terms point) n) (λ point → terms point n)
    (partialSumFamilyIsRadiuswiseUniformlyContinuous source terms term-uc n)
    (term-uc n)


-- A uniform tail and one finite sum suffice at each requested precision.
-- This does not convert radiuswise existence into a selected modulus.
uniformSeriesValueIsRadiuswiseUniformlyContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
    (terms : A → RealSequence) (uniform : UniformlyCauchySeries A terms) →
  (∀ n → IsRadiuswiseUniformlyContinuous source
    (λ point → terms point n) (ℝPremetricSpace .snd)) →
  IsRadiuswiseUniformlyContinuous source
    (uniformSeriesValue terms uniform) (ℝPremetricSpace .snd)
uniformSeriesValueIsRadiuswiseUniformlyContinuous
    {A = A} source terms uniform term-uc ε =
  PT.rec squash₁ useCutoff
    (uniformlyCauchySeriesHasUniformSum terms uniform (ε /4₊))
  where
  value : A → ℝ
  value = uniformSeriesValue terms uniform

  useCutoff :
    (Σ[ cutoff ∈ ℕ ] (∀ x n → cutoff ℕ.≤ n →
      partialSum (terms x) n ∼[ ε /4₊ ] value x)) →
    ∃[ δ ∈ ℚ₊ ] (∀ x y → PremetricStr._≈[_]_ source x δ y →
      value x ∼[ ε ] value y)
  useCutoff (cutoff , tail) =
    PT.map (λ { (δ , partial-close) →
      δ , λ x y near →
        Pℝ.subst≈ (value x) (value y) (quarterHalfQuarter ε)
          (triangle∼ (value x) (partialSum (terms x) cutoff) (value y)
            (ε /4₊) ((ε /2₊) +₊ (ε /4₊))
            (sym∼ (partialSum (terms x) cutoff) (value x) (ε /4₊)
              (tail x cutoff ℕ.≤-refl))
            (triangle∼ (partialSum (terms x) cutoff)
              (partialSum (terms y) cutoff) (value y) (ε /2₊) (ε /4₊)
              (partial-close x y near) (tail y cutoff ℕ.≤-refl))) })
      (partialSumFamilyIsRadiuswiseUniformlyContinuous
        source terms term-uc cutoff (ε /2₊))


private
  powerBound : ∀ {ℓ} {A : Type ℓ} (f : A → ℝ) radius →
    (∀ x → absℝ (f x) ≤ℝ radius) →
    ∀ n x → absℝ (powℝ (f x) n) ≤ℝ powℝ radius n
  powerBound f radius bounded n x =
    subst (_≤ℝ powℝ radius n) (sym (absPow (f x) n))
      (powMono n (absNonnegative (f x)) (bounded x))

  boundedPowerIsRadiuswiseUniformlyContinuous :
    ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
      (f : A → ℝ) radius →
    (∀ x → absℝ (f x) ≤ℝ radius) →
    IsRadiuswiseUniformlyContinuous source f (ℝPremetricSpace .snd) →
    ∀ n → IsRadiuswiseUniformlyContinuous source
      (λ x → powℝ (f x) n) (ℝPremetricSpace .snd)
  boundedPowerIsRadiuswiseUniformlyContinuous source f radius bounded f-uc zero =
    constantIsRadiuswiseUniformlyContinuous source 1ℝ
  boundedPowerIsRadiuswiseUniformlyContinuous source f radius bounded f-uc (suc n) =
    boundedProductIsRadiuswiseUniformlyContinuous source
      f (λ x → powℝ (f x) n) radius (powℝ radius n)
      bounded (powerBound f radius bounded n) f-uc
      (boundedPowerIsRadiuswiseUniformlyContinuous source f radius bounded f-uc n)


module _ (radius : ℝ) (0≤radius : 0ℝ ≤ℝ radius) where
  private
    source = ClosedAbsRadiusPairPremetricSpace radius .snd
    left = closedAbsRadiusPairLeft radius
    right = closedAbsRadiusPairRight radius

    left-uc : IsRadiuswiseUniformlyContinuous source left (ℝPremetricSpace .snd)
    left-uc ε = ∣ ε , (λ x y near → fst near) ∣₁

    right-uc : IsRadiuswiseUniformlyContinuous source right (ℝPremetricSpace .snd)
    right-uc ε = ∣ ε , (λ x y near → snd near) ∣₁

    factor-bound : ∀ n point →
      absℝ (powerDifferenceFactor (left point) (right point) n) ≤ℝ
      realNatural (suc n) · powℝ radius n
    factor-bound n point =
      powerDifferenceFactor-bound (left point) (right point) radius 0≤radius
        (snd (fst point)) (snd (snd point)) n

    factor-uc : ∀ n → IsRadiuswiseUniformlyContinuous source
      (λ point → powerDifferenceFactor (left point) (right point) n)
      (ℝPremetricSpace .snd)
    factor-uc zero = constantIsRadiuswiseUniformlyContinuous source 1ℝ
    factor-uc (suc n) =
      sumIsRadiuswiseUniformlyContinuous source
        (λ point → powℝ (right point) (suc n))
        (λ point → left point · powerDifferenceFactor (left point) (right point) n)
        (boundedPowerIsRadiuswiseUniformlyContinuous source right radius
          (λ point → snd (snd point)) right-uc (suc n))
        (boundedProductIsRadiuswiseUniformlyContinuous source
          left (λ point → powerDifferenceFactor (left point) (right point) n)
          radius (realNatural (suc n) · powℝ radius n)
          (λ point → snd (fst point)) (factor-bound n) left-uc (factor-uc n))

  powerSeriesDifferenceFactorTermIsRadiuswiseUniformlyContinuous :
    ∀ coefficients n → IsRadiuswiseUniformlyContinuous source
      (λ point → powerSeriesDifferenceFactorOnClosedRadius coefficients radius point n)
      (ℝPremetricSpace .snd)
  powerSeriesDifferenceFactorTermIsRadiuswiseUniformlyContinuous coefficients n =
    boundedProductIsRadiuswiseUniformlyContinuous source
      (λ _ → coefficients (suc n))
      (λ point → powerDifferenceFactor (left point) (right point) n)
      (absℝ (coefficients (suc n))) (realNatural (suc n) · powℝ radius n)
      (λ _ → ≤ℝ-refl (absℝ (coefficients (suc n)))) (factor-bound n)
      (constantIsRadiuswiseUniformlyContinuous source (coefficients (suc n)))
      (factor-uc n)

  powerSeriesDifferenceFactorValueIsRadiuswiseUniformlyContinuous :
    ∀ coefficients
      (factor-uniform : PowerSeriesDifferenceFactorUniformlyCauchyOnRadius coefficients radius) →
    IsRadiuswiseUniformlyContinuous source
      (powerSeriesDifferenceFactorValueOnClosedRadius coefficients radius factor-uniform)
      (ℝPremetricSpace .snd)
  powerSeriesDifferenceFactorValueIsRadiuswiseUniformlyContinuous coefficients factor-uniform =
    uniformSeriesValueIsRadiuswiseUniformlyContinuous source
      (powerSeriesDifferenceFactorOnClosedRadius coefficients radius) factor-uniform
      (powerSeriesDifferenceFactorTermIsRadiuswiseUniformlyContinuous coefficients)
