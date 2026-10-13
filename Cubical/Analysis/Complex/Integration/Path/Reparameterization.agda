module Cubical.Analysis.Complex.Integration.Path.Reparameterization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AbsoluteValue using (absℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_; mul-rat)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform using (IsRadiuswiseUniformDerivativeOn)
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform.Estimates
open import Cubical.Analysis.Real.Integration.UniformContinuity
import Cubical.Analysis.Real.Integration.FundamentalTheorem.Substitution as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Algebra.RealScalar
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Integration.Curve
open import Cubical.Analysis.Complex.Integration.Path
import Cubical.Analysis.Complex.Integration.Path.Structure as Structure

private
  module Data = Structure.PathStructure ℝ ℝ ℚ₊ _≤ℝ_ IsRadiuswiseUniformDerivativeOn
    (λ velocity a b B → ∀ t → a ≤ℝ t → t ≤ℝ b → absℝ (velocity t) ≤ℝ rat (fst B))

open Data public using () renaming (UniformPath to UniformParameterChange)

-- A change need not be monotone or injective. The supplied image bounds
-- ensure that only certified points of the original path are used.
module _ {a b c d : ℝ} (path : UniformComplexPath c d) (change : UniformParameterChange a b)
  (imageLower : ∀ t → a ≤ℝ t → t ≤ℝ b → c ≤ℝ UniformParameterChange.curve change t)
  (imageUpper : ∀ t → a ≤ℝ t → t ≤ℝ b → UniformParameterChange.curve change t ≤ℝ d) where
  private
    module P = UniformComplexPath path
    module T = UniformParameterChange change

  parameterChangeImage : ClosedInterval a b → ClosedInterval c d
  parameterChangeImage (t , lo , hi) = T.curve t , imageLower t lo hi , imageUpper t lo hi

  parameterChangeImageIsUniformlyContinuous : IsRadiuswiseUniformlyContinuous
    (ClosedIntervalPremetricSpace a b .snd) parameterChangeImage (ClosedIntervalPremetricSpace c d .snd)
  parameterChangeImageIsUniformlyContinuous =
    boundedUniformDerivativeGivesUniformContinuityOn T.curve T.velocity a b T.speedBound T.differentiable T.boundedSpeed

  opaque
    reparameterizedCurveDerivative : IsUniformComplexCurveDerivativeOn (P.curve ∘ T.curve)
      (λ t → P.velocity (T.curve t) ·ℂ fromℝ (T.velocity t)) a b
    reparameterizedCurveDerivative =
      subst (λ v → IsUniformComplexCurveDerivativeOn (P.curve ∘ T.curve) v a b)
        (sym (funExt (λ t → complexMultiplyReal (P.velocity (T.curve t)) (T.velocity t))))
        (Real.compositeHasUniformDerivativeOn (re ∘ P.curve) (re ∘ P.velocity) T.curve T.velocity
          a b c d T.ordered P.ordered P.speedBound T.speedBound (fst P.differentiable) T.differentiable
          (λ t lo hi → ≤ℝ-trans (absℝ (re (P.velocity t))) (normℂ (P.velocity t)) (rat (fst P.speedBound))
            (reAbs≤normℂ (P.velocity t)) (P.boundedSpeed t lo hi)) T.boundedSpeed imageLower imageUpper ,
         Real.compositeHasUniformDerivativeOn (im ∘ P.curve) (im ∘ P.velocity) T.curve T.velocity
          a b c d T.ordered P.ordered P.speedBound T.speedBound (snd P.differentiable) T.differentiable
          (λ t lo hi → ≤ℝ-trans (absℝ (im (P.velocity t))) (normℂ (P.velocity t)) (rat (fst P.speedBound))
            (imAbs≤normℂ (P.velocity t)) (P.boundedSpeed t lo hi)) T.boundedSpeed imageLower imageUpper)

  reparameterizeComplexPath : UniformComplexPath a b
  reparameterizeComplexPath .UniformComplexPath.ordered = T.ordered
  reparameterizeComplexPath .UniformComplexPath.curve = P.curve ∘ T.curve
  reparameterizeComplexPath .UniformComplexPath.velocity t = P.velocity (T.curve t) ·ℂ fromℝ (T.velocity t)
  reparameterizeComplexPath .UniformComplexPath.differentiable = reparameterizedCurveDerivative
  reparameterizeComplexPath .UniformComplexPath.speedBound = P.speedBound ·₊ T.speedBound
  reparameterizeComplexPath .UniformComplexPath.boundedSpeed t lo hi =
    subst (normℂ (P.velocity (T.curve t) ·ℂ fromℝ (T.velocity t)) ≤ℝ_)
      (mul-rat (fst P.speedBound) (fst T.speedBound))
      (normℂ-mulBound (P.velocity (T.curve t)) (fromℝ (T.velocity t))
        (rat (fst P.speedBound)) (rat (fst T.speedBound))
        (P.boundedSpeed (T.curve t) (imageLower t lo hi) (imageUpper t lo hi))
        (subst (_≤ℝ rat (fst T.speedBound)) (sym (normℂ-fromℝ (T.velocity t))) (T.boundedSpeed t lo hi)))
