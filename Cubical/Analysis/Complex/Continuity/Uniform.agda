module Cubical.Analysis.Complex.Continuity.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue using (absℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Integration.UniformContinuity
import Cubical.Analysis.Real.Series.PowerSeries.Difference.UniformDerivative.Continuity as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric

-- Finite combinations of radiuswise witnesses stay under truncation. These
-- operations do not choose a function of all tolerances.
module _ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A) where
  reComplexUniform : (f : A → ℂ) →
    IsRadiuswiseUniformlyContinuous source f (ℂPremetricSpace .snd) →
    IsRadiuswiseUniformlyContinuous source (re ∘ f) (ℝPremetricSpace .snd)
  reComplexUniform f uniform ε = PT.map
    (λ { (δ , near) → δ , λ x y close → fst (near x y close) }) (uniform ε)

  imComplexUniform : (f : A → ℂ) →
    IsRadiuswiseUniformlyContinuous source f (ℂPremetricSpace .snd) →
    IsRadiuswiseUniformlyContinuous source (im ∘ f) (ℝPremetricSpace .snd)
  imComplexUniform f uniform ε = PT.map
    (λ { (δ , near) → δ , λ x y close → snd (near x y close) }) (uniform ε)

  pairComplexUniform : (f g : A → ℝ) →
    IsRadiuswiseUniformlyContinuous source f (ℝPremetricSpace .snd) →
    IsRadiuswiseUniformlyContinuous source g (ℝPremetricSpace .snd) →
    IsRadiuswiseUniformlyContinuous source (λ x → f x , g x) (ℂPremetricSpace .snd)
  pairComplexUniform f g uf ug ε = PT.map2
    (λ { (δ , nf) (η , ng) → min₊ δ η , λ x y close →
      nf x y (PremetricStr.isMonotone≈≤ source x y (min₊ δ η) δ (min₊≤L δ η) close) ,
      ng x y (PremetricStr.isMonotone≈≤ source x y (min₊ δ η) η (min₊≤R δ η) close) }) (uf ε) (ug ε)

  constantComplexUniform : ∀ z →
    IsRadiuswiseUniformlyContinuous source (λ (_ : A) → z) (ℂPremetricSpace .snd)
  constantComplexUniform z = pairComplexUniform (λ _ → re z) (λ _ → im z)
    (Real.constantIsRadiuswiseUniformlyContinuous source (re z))
    (Real.constantIsRadiuswiseUniformlyContinuous source (im z))

  sumComplexUniform : ∀ f g →
    IsRadiuswiseUniformlyContinuous source f (ℂPremetricSpace .snd) →
    IsRadiuswiseUniformlyContinuous source g (ℂPremetricSpace .snd) →
    IsRadiuswiseUniformlyContinuous source (λ x → f x +ℂ g x) (ℂPremetricSpace .snd)
  sumComplexUniform f g uf ug = pairComplexUniform (λ x → re (f x) + re (g x)) (λ x → im (f x) + im (g x))
    (Real.sumIsRadiuswiseUniformlyContinuous source (re ∘ f) (re ∘ g) (reComplexUniform f uf) (reComplexUniform g ug))
    (Real.sumIsRadiuswiseUniformlyContinuous source (im ∘ f) (im ∘ g) (imComplexUniform f uf) (imComplexUniform g ug))

  opaque
    boundedProductComplexUniform : ∀ f g B C →
      (∀ x → normℂ (f x) ≤ℝ B) → (∀ x → normℂ (g x) ≤ℝ C) →
      IsRadiuswiseUniformlyContinuous source f (ℂPremetricSpace .snd) →
      IsRadiuswiseUniformlyContinuous source g (ℂPremetricSpace .snd) →
      IsRadiuswiseUniformlyContinuous source (λ x → f x ·ℂ g x) (ℂPremetricSpace .snd)
    boundedProductComplexUniform f g B C bf bg uf ug = pairComplexUniform _ _
      (Real.sumIsRadiuswiseUniformlyContinuous source _ _ rr
        (λ ε → PT.map (λ { (δ , near) → δ , λ x y close →
          IsNonExpanding.pres≈ neg-isNonExpanding _ _ ε (near x y close) }) (ii ε)))
      (Real.sumIsRadiuswiseUniformlyContinuous source _ _ ri ir)
      where
      rf : ∀ x → absℝ (re (f x)) ≤ℝ B
      rf x = ≤ℝ-trans (absℝ (re (f x))) (normℂ (f x)) B (reAbs≤normℂ (f x)) (bf x)
      if' : ∀ x → absℝ (im (f x)) ≤ℝ B
      if' x = ≤ℝ-trans (absℝ (im (f x))) (normℂ (f x)) B (imAbs≤normℂ (f x)) (bf x)
      rg : ∀ x → absℝ (re (g x)) ≤ℝ C
      rg x = ≤ℝ-trans (absℝ (re (g x))) (normℂ (g x)) C (reAbs≤normℂ (g x)) (bg x)
      ig : ∀ x → absℝ (im (g x)) ≤ℝ C
      ig x = ≤ℝ-trans (absℝ (im (g x))) (normℂ (g x)) C (imAbs≤normℂ (g x)) (bg x)
      rr : IsRadiuswiseUniformlyContinuous source (λ x → re (f x) · re (g x)) (ℝPremetricSpace .snd)
      rr = Real.boundedProductIsRadiuswiseUniformlyContinuous source (re ∘ f) (re ∘ g) B C rf rg
        (reComplexUniform f uf) (reComplexUniform g ug)
      ii : IsRadiuswiseUniformlyContinuous source (λ x → im (f x) · im (g x)) (ℝPremetricSpace .snd)
      ii = Real.boundedProductIsRadiuswiseUniformlyContinuous source (im ∘ f) (im ∘ g) B C if' ig
        (imComplexUniform f uf) (imComplexUniform g ug)
      ri : IsRadiuswiseUniformlyContinuous source (λ x → re (f x) · im (g x)) (ℝPremetricSpace .snd)
      ri = Real.boundedProductIsRadiuswiseUniformlyContinuous source (re ∘ f) (im ∘ g) B C rf ig
        (reComplexUniform f uf) (imComplexUniform g ug)
      ir : IsRadiuswiseUniformlyContinuous source (λ x → im (f x) · re (g x)) (ℝPremetricSpace .snd)
      ir = Real.boundedProductIsRadiuswiseUniformlyContinuous source (im ∘ f) (re ∘ g) B C if' rg
        (imComplexUniform f uf) (reComplexUniform g ug)
