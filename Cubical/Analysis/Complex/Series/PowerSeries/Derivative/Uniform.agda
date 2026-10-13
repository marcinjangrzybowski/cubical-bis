module Cubical.Analysis.Complex.Series.PowerSeries.Derivative.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Analysis.Real.Order.Base
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Uniform
open import Cubical.Analysis.Complex.Series.Uniform.Continuity
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Sum
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Uniform
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Factor

-- Joint uniform continuity of the factor gives the quantitative derivative
-- estimate needed by the existing FTC. No compactness upgrade is used.
opaque
  complexPowerSeriesHasUniformFormalDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate f d : A → ℂ) coefficients radius →
    (∀ x → normℂ (coordinate x) ≤ℝ radius) →
    Real.IsCauchySeries (complexPowerSeriesDerivativeMajorant coefficients radius) →
    IsRadiuswiseUniformlyContinuous source coordinate (ℂPremetricSpace .snd) →
    (∀ x → HasComplexSum (powerSeriesTermsℂ coefficients (coordinate x)) (f x)) →
    (∀ x → HasComplexSum (powerSeriesTermsℂ (formalDerivativeℂ coefficients) (coordinate x)) (d x)) →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate f d
  complexPowerSeriesHasUniformFormalDerivativeAlong {ℓ' = ℓ'} {A = A} source coordinate f d coefficients radius bounded witness continuous fs ds =
    uniformlyContinuousComplexDifferenceFactorGivesUniformDerivative source coordinate f d factor
      (λ x y → powerSeriesValueℂDifferenceFactorization coefficients (coordinate x) (coordinate y)
        (f x) (f y) (factor (x , y)) (fs x) (fs y) (factorSum (x , y))
        ∙ ·ℂComm (coordinate y -ℂ coordinate x) (factor (x , y)))
      (λ x → powerSeriesDifferenceFactorℂDiagonalValue coefficients (coordinate x)
        (factor (x , x)) (d x) (factorSum (x , x)) (ds x))
      (uniformComplexSeriesValueIsRadiuswiseUniformlyContinuous pairSource terms uniform
        (powerSeriesDifferenceFactorℂUniform pairSource coefficients left right radius
          (λ p → bounded (fst p)) (λ p → bounded (snd p)) leftUniform rightUniform))
    where
    pairSource : PremetricStr ℓ' (A × A)
    pairSource = PremetricProductStr source source
    left right : A × A → ℂ
    left p = coordinate (fst p)
    right p = coordinate (snd p)
    terms : A × A → ComplexSequence
    terms p = powerSeriesDifferenceFactorℂ coefficients (left p) (right p)
    uniform : UniformlyComplexCauchySeries (A × A) terms
    uniform = powerSeriesDifferenceFactorℂUniformlyCauchy coefficients left right radius
      (λ p → bounded (fst p)) (λ p → bounded (snd p)) witness
    factor : A × A → ℂ
    factor = uniformComplexSeriesValue terms uniform
    factorSum : ∀ p → HasComplexSum (terms p) (factor p)
    factorSum = uniformHasComplexSumAt (uniformlyComplexCauchySeriesHasUniformSum terms uniform)
    leftUniform : IsRadiuswiseUniformlyContinuous pairSource left (ℂPremetricSpace .snd)
    leftUniform ε = PT.map (λ { (δ , near) → δ , λ p q close → near (fst p) (fst q) (fst close) }) (continuous ε)
    rightUniform : IsRadiuswiseUniformlyContinuous pairSource right (ℂPremetricSpace .snd)
    rightUniform ε = PT.map (λ { (δ , near) → δ , λ p q close → near (snd p) (snd q) (snd close) }) (continuous ε)
