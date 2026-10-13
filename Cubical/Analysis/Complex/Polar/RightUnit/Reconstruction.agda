module Cubical.Analysis.Complex.Polar.RightUnit.Reconstruction where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Functions.SquareRoot.Order
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pythagorean
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Value
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Polar.Cis
import Cubical.Analysis.Complex.Polar.Algebra as AlgebraDefinition

opaque
  cosine-positive-in-quarter : ∀ θ → (- halfPiℝ) <ℝ θ → θ <ℝ halfPiℝ → 0ℝ <ℝ cosℝ θ
  cosine-positive-in-quarter = characterizedCosine-positive-inside halfPiℝ halfPiℝ-characterization

  reconstructUnitCosine : ∀ a b θ → 0ℝ <ℝ a → a · a + b · b ≡ 1ℝ →
    (- halfPiℝ) <ℝ θ → θ <ℝ halfPiℝ → sinℝ θ ≡ b → cosℝ θ ≡ a
  reconstructUnitCosine a b θ positive unit lower upper sine =
    squareInjectiveNonnegative (cosℝ θ) a
      (<ℝ-weaken 0ℝ (cosℝ θ) (cosine-positive-in-quarter θ lower upper))
      (<ℝ-weaken 0ℝ a positive)
      (AlgebraDefinition.PolarAlgebra.otherSquare ℝCommRing a b (cosℝ θ) (sinℝ θ)
        unit (sin²+cos²≡1 θ) sine)

private
  opaque
    composeCoordinates : (z : ℂ) (a b c d : ℝ) →
      z ≡ (a , b) → a ≡ c → b ≡ d → z ≡ (c , d)
    composeCoordinates z a b c d p q r = p ∙ ℂ≡ q r

opaque
  reconstructUnit : ∀ a b θ → 0ℝ <ℝ a → a · a + b · b ≡ 1ℝ →
    (- halfPiℝ) <ℝ θ → θ <ℝ halfPiℝ → sinℝ θ ≡ b → cisℝ θ ≡ (a , b)
  reconstructUnit a b θ positive unit lower upper sine =
    composeCoordinates (cisℝ θ) (cosℝ θ) (sinℝ θ) a b (cisℝ-value θ)
      (reconstructUnitCosine a b θ positive unit lower upper sine) sine
