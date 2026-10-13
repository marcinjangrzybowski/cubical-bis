module Cubical.Analysis.Complex.Calculus.Derivative.Uniform.RealParameter where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (addPres≤)
import Cubical.Analysis.Real.Calculus.Derivative.Base as Real
import Cubical.Analysis.Real.Calculus.Derivative.Uniform as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Algebra.RealScalar
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Estimates using (halfErrorSum)
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform

opaque
  realParameterDisplacementNorm : ∀ {ℓ} {A : Type ℓ} (coordinate : A → ℝ) x y →
    normℂ (fromℝ (coordinate y) -ℂ fromℝ (coordinate x)) ≡ absℝ (coordinate y - coordinate x)
  realParameterDisplacementNorm coordinate x y =
    cong normℂ (fromℝDifference (coordinate y) (coordinate x)) ∙ normℂ-fromℝ (coordinate y - coordinate x)

  realParameterErrorCoordinates : ∀ {ℓ} {A : Type ℓ} (coordinate : A → ℝ) (f d : A → ℂ) x y →
    complexDerivativeErrorAlong (fromℝ ∘ coordinate) f (d x) x y ≡
      (Real.derivativeErrorAlong coordinate (re ∘ f) (re ∘ d) x y ,
       Real.derivativeErrorAlong coordinate (im ∘ f) (im ∘ d) x y)
  realParameterErrorCoordinates coordinate f d x y =
    cong (λ v → (f y -ℂ f x) -ℂ v)
      (cong (d x ·ℂ_) (fromℝDifference (coordinate y) (coordinate x))
        ∙ complexMultiplyReal (d x) (coordinate y - coordinate x))

-- A complex curve derivative is exactly the two real coordinate
-- derivatives. This bridge is about a real parameter, not a claim that
-- arbitrary pairs of real partial derivatives give holomorphicity.
opaque
  uniformRealCoordinates→complexDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate : A → ℝ) (f d : A → ℂ) →
    Real.IsRadiuswiseUniformDerivativeAlong source coordinate (re ∘ f) (re ∘ d) →
    Real.IsRadiuswiseUniformDerivativeAlong source coordinate (im ∘ f) (im ∘ d) →
    IsRadiuswiseUniformComplexDerivativeAlong source (fromℝ ∘ coordinate) f d
  uniformRealCoordinates→complexDerivativeAlong source coordinate f d first second ε = PT.map2
    (λ { (δ , r) (η , s) → min₊ δ η , λ x y close →
      subst2 _≤ℝ_
        (sym (cong normℂ (realParameterErrorCoordinates coordinate f d x y)))
        (halfErrorSum ε (absℝ (coordinate y - coordinate x))
          ∙ sym (cong (rat (fst ε) ·_) (realParameterDisplacementNorm coordinate x y)))
        (addPres≤
          (absℝ (Real.derivativeErrorAlong coordinate (re ∘ f) (re ∘ d) x y))
          (rat (fst (ε /2₊)) · absℝ (coordinate y - coordinate x))
          (absℝ (Real.derivativeErrorAlong coordinate (im ∘ f) (im ∘ d) x y))
          (rat (fst (ε /2₊)) · absℝ (coordinate y - coordinate x))
          (r x y (PremetricStr.isMonotone≈≤ source x y (min₊ δ η) δ (min₊≤L δ η) close))
          (s x y (PremetricStr.isMonotone≈≤ source x y (min₊ δ η) η (min₊≤R δ η) close))) })
    (first (ε /2₊)) (second (ε /2₊))

  uniformComplexDerivativeAlong→realCoordinates : ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (coordinate : A → ℝ) (f d : A → ℂ) →
    IsRadiuswiseUniformComplexDerivativeAlong source (fromℝ ∘ coordinate) f d →
    Real.IsRadiuswiseUniformDerivativeAlong source coordinate (re ∘ f) (re ∘ d) ×
    Real.IsRadiuswiseUniformDerivativeAlong source coordinate (im ∘ f) (im ∘ d)
  uniformComplexDerivativeAlong→realCoordinates source coordinate f d derivative =
    (λ ε → PT.map (λ { (δ , near) → δ , λ x y close →
      subst2 _≤ℝ_ (cong (absℝ ∘ re) (realParameterErrorCoordinates coordinate f d x y))
        (cong (rat (fst ε) ·_) (realParameterDisplacementNorm coordinate x y))
        (≤ℝ-trans (absℝ (re (complexDerivativeErrorAlong (fromℝ ∘ coordinate) f (d x) x y)))
          (normℂ (complexDerivativeErrorAlong (fromℝ ∘ coordinate) f (d x) x y))
          (rat (fst ε) · normℂ (fromℝ (coordinate y) -ℂ fromℝ (coordinate x)))
          (reAbs≤normℂ (complexDerivativeErrorAlong (fromℝ ∘ coordinate) f (d x) x y)) (near x y close)) })
      (derivative ε)) ,
    (λ ε → PT.map (λ { (δ , near) → δ , λ x y close →
      subst2 _≤ℝ_ (cong (absℝ ∘ im) (realParameterErrorCoordinates coordinate f d x y))
        (cong (rat (fst ε) ·_) (realParameterDisplacementNorm coordinate x y))
        (≤ℝ-trans (absℝ (im (complexDerivativeErrorAlong (fromℝ ∘ coordinate) f (d x) x y)))
          (normℂ (complexDerivativeErrorAlong (fromℝ ∘ coordinate) f (d x) x y))
          (rat (fst ε) · normℂ (fromℝ (coordinate y) -ℂ fromℝ (coordinate x)))
          (imAbs≤normℂ (complexDerivativeErrorAlong (fromℝ ∘ coordinate) f (d x) x y)) (near x y close)) })
      (derivative ε))
