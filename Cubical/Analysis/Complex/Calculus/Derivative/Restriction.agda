module Cubical.Analysis.Complex.Calculus.Derivative.Restriction where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Algebra.RealScalar
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Calculus.Derivative.Base

-- Restriction is a consequence of complex differentiability. Separate
-- horizontal derivatives alone are not a definition of holomorphicity.
horizontalComplexLine : ℂ → ℝ → ℂ
horizontalComplexLine z t = t , im z

private
  displacement : ∀ z t → horizontalComplexLine z t -ℂ z ≡ fromℝ (t - re z)
  displacement z t = ℂ≡ refl (subSelf (im z))

  horizontalError : ∀ f d z t →
    complexDerivativeErrorAlong (idfun ℂ) f d z (horizontalComplexLine z t) ≡
      ((re (f (horizontalComplexLine z t)) - re (f z)) - re d · (t - re z) ,
       (im (f (horizontalComplexLine z t)) - im (f z)) - im d · (t - re z))
  horizontalError f d z t = cong (λ v → (f (horizontalComplexLine z t) -ℂ f z) -ℂ v)
    (cong (d ·ℂ_) (displacement z t) ∙ complexMultiplyReal d (t - re z))

opaque
  complexDerivativeHorizontalRealAt : ∀ f d z → IsComplexDerivativeAt f d z →
    IsDerivativeAt (re ∘ f ∘ horizontalComplexLine z) (re d) (re z)
  complexDerivativeHorizontalRealAt f d z differentiable ε = PT.map
    (λ { (δ , near) → δ , λ t close →
      subst2 _≤ℝ_ (cong (absℝ ∘ re) (horizontalError f d z t))
        (cong (rat (fst ε) ·_) (cong normℂ (displacement z t) ∙ normℂ-fromℝ (t - re z)))
        (≤ℝ-trans (absℝ (re (complexDerivativeErrorAlong (idfun ℂ) f d z (horizontalComplexLine z t))))
          (normℂ (complexDerivativeErrorAlong (idfun ℂ) f d z (horizontalComplexLine z t)))
          (rat (fst ε) · normℂ (horizontalComplexLine z t -ℂ z))
          (reAbs≤normℂ (complexDerivativeErrorAlong (idfun ℂ) f d z (horizontalComplexLine z t)))
          (near (horizontalComplexLine z t) (close , refl∼ (im z) δ))) })
    (differentiable ε)

  complexDerivativeHorizontalImaginaryAt : ∀ f d z → IsComplexDerivativeAt f d z →
    IsDerivativeAt (im ∘ f ∘ horizontalComplexLine z) (im d) (re z)
  complexDerivativeHorizontalImaginaryAt f d z differentiable ε = PT.map
    (λ { (δ , near) → δ , λ t close →
      subst2 _≤ℝ_ (cong (absℝ ∘ im) (horizontalError f d z t))
        (cong (rat (fst ε) ·_) (cong normℂ (displacement z t) ∙ normℂ-fromℝ (t - re z)))
        (≤ℝ-trans (absℝ (im (complexDerivativeErrorAlong (idfun ℂ) f d z (horizontalComplexLine z t))))
          (normℂ (complexDerivativeErrorAlong (idfun ℂ) f d z (horizontalComplexLine z t)))
          (rat (fst ε) · normℂ (horizontalComplexLine z t -ℂ z))
          (imAbs≤normℂ (complexDerivativeErrorAlong (idfun ℂ) f d z (horizontalComplexLine z t)))
          (near (horizontalComplexLine z t) (close , refl∼ (im z) δ))) })
    (differentiable ε)
