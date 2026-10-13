module Cubical.Analysis.Complex.Calculus.Derivative.SmallError where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Inverse
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.HITs.PropositionalTruncation.Monad
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Estimates

-- Local little-o estimates used by the derivative rules. No family of radii
-- is chosen: all the combinations below take place inside truncations.
IsSmallComplexErrorAt : ∀ {ℓ ℓ'} {A : Type ℓ} → PremetricStr ℓ' A →
  A → (displacement error : A → ℂ) → Type (ℓ-max ℓ ℓ')
IsSmallComplexErrorAt source x displacement error = ∀ (ε : ℚ₊) →
  ∃[ δ ∈ ℚ₊ ] (∀ y → PremetricStr._≈[_]_ source x δ y →
    normℂ (error y) ≤ℝ rat (fst ε) · normℂ (displacement y))

module _ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A) (x : A)
  (displacement : A → ℂ) where
  private
    module P = PremetricStr source

  opaque
    smallComplexErrorCong : ∀ e f → (∀ y → e y ≡ f y) →
      IsSmallComplexErrorAt source x displacement e → IsSmallComplexErrorAt source x displacement f
    smallComplexErrorCong e f equal small ε = do
      (δ , near) ← small ε
      return (δ , λ y close → subst (λ v → normℂ v ≤ℝ rat (fst ε) · normℂ (displacement y))
        (equal y) (near y close))

    smallComplexErrorAdd : ∀ e f →
      IsSmallComplexErrorAt source x displacement e → IsSmallComplexErrorAt source x displacement f →
      IsSmallComplexErrorAt source x displacement (λ y → e y +ℂ f y)
    smallComplexErrorAdd e f first second ε = do
      (δ , nearE) ← first (ε /2₊)
      (η , nearF) ← second (ε /2₊)
      return (min₊ δ η , λ y close →
        subst (normℂ (e y +ℂ f y) ≤ℝ_) (halfErrorSum ε (normℂ (displacement y)))
          (normℂ-addBound (e y) (f y)
            (rat (fst (ε /2₊)) · normℂ (displacement y)) (rat (fst (ε /2₊)) · normℂ (displacement y))
            (nearE y (P.isMonotone≈≤ x y (min₊ δ η) δ (min₊≤L δ η) close))
            (nearF y (P.isMonotone≈≤ x y (min₊ δ η) η (min₊≤R δ η) close))))

    smallComplexErrorNeg : ∀ e → IsSmallComplexErrorAt source x displacement e →
      IsSmallComplexErrorAt source x displacement (λ y → -ℂ e y)
    smallComplexErrorNeg e small ε = do
      (δ , near) ← small ε
      return (δ , λ y close → subst (_≤ℝ rat (fst ε) · normℂ (displacement y))
        (sym (normℂ-neg (e y))) (near y close))

  opaque
    smallComplexErrorMulBounded : (g e : A → ℂ) → ∀ (B δ : ℚ₊) →
      (∀ y → P._≈[_]_ x δ y → normℂ (g y) ≤ℝ rat (fst B)) →
      IsSmallComplexErrorAt source x displacement e →
      IsSmallComplexErrorAt source x displacement (λ y → g y ·ℂ e y)
    smallComplexErrorMulBounded g e B δ bounded small ε = PT.map combine (small (ε ₊／₊ B))
      where
      combine :
        (Σ[ η ∈ ℚ₊ ] (∀ y → P._≈[_]_ x η y →
          normℂ (e y) ≤ℝ rat (fst (ε ₊／₊ B)) · normℂ (displacement y))) →
        (Σ[ η ∈ ℚ₊ ] (∀ y → P._≈[_]_ x η y →
          normℂ (g y ·ℂ e y) ≤ℝ rat (fst ε) · normℂ (displacement y)))
      combine (η , near) = min₊ δ η , λ y close →
        boundedComplexErrorProduct (g y) (e y) (normℂ (displacement y)) B ε
          (bounded y (P.isMonotone≈≤ x y (min₊ δ η) δ (min₊≤L δ η) close))
          (near y (P.isMonotone≈≤ x y (min₊ δ η) η (min₊≤R δ η) close))
  opaque
    smallComplexErrorMulContinuous : (g e : A → ℂ) → IsContinuousAt source g (ℂPremetricSpace .snd) x →
      IsSmallComplexErrorAt source x displacement e →
      IsSmallComplexErrorAt source x displacement (λ y → g y ·ℂ e y)
    smallComplexErrorMulContinuous g e continuous small ε = do
      (B , local) ← continuousComplexNormBoundAt source g x continuous
      (δ , bounded) ← local
      smallComplexErrorMulBounded g e B δ bounded small ε

  opaque
    smallComplexErrorMulConstant : (c : ℂ) (e : A → ℂ) → IsSmallComplexErrorAt source x displacement e →
      IsSmallComplexErrorAt source x displacement (λ y → c ·ℂ e y)
    smallComplexErrorMulConstant c e small ε = do
      (B , bounded) ← complexNormRationalBound c
      smallComplexErrorMulBounded (λ _ → c) e B ε (λ _ _ → bounded) small ε

  opaque
    smallComplexErrorContinuousFactor : (g : A → ℂ) → IsContinuousAt source g (ℂPremetricSpace .snd) x →
      IsSmallComplexErrorAt source x displacement (λ y → (g y -ℂ g x) ·ℂ displacement y)
    smallComplexErrorContinuousFactor g continuous ε = do
      (δ , near) ← continuousComplexNormDifferenceAt source g x continuous ε
      return (δ , λ y close → normℂ-mulBound (g y -ℂ g x) (displacement y)
        (rat (fst ε)) (normℂ (displacement y))
        (<ℝ-weaken (normℂ (g y -ℂ g x)) (rat (fst ε)) (near y close))
        (≤ℝ-refl (normℂ (displacement y))))
