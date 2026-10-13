module Cubical.Analysis.Complex.Polynomial.Newton.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
import Cubical.Analysis.Complex.Polynomial.Newton.Algebra as NewtonDefinition

private module C = NewtonDefinition.NewtonIdentities ℂCommRing

opaque
  newtonDifferenceBound : ∀ inverse derivative → inverse ·ℂ derivative ≡ 1ℂ →
    ∀ z w pz pw error q →
    normℂ inverse · error ≤ℝ q →
    normℂ ((pz -ℂ pw) -ℂ derivative ·ℂ (z -ℂ w)) ≤ℝ error · normℂ (z -ℂ w) →
    normℂ ((z -ℂ inverse ·ℂ pz) -ℂ (w -ℂ inverse ·ℂ pw)) ≤ℝ q · normℂ (z -ℂ w)
  newtonDifferenceBound inverse derivative inverseLaw z w pz pw error q inverseBound remainderBound =
    subst (_≤ℝ q · distance)
      (sym (cong normℂ (C.difference inverse derivative inverseLaw z w pz pw)))
      (≤ℝ-trans (normℂ ((-ℂ inverse) ·ℂ remainder)) (normℂ inverse · (error · distance))
        (q · distance)
        (normℂ-mulBound (-ℂ inverse) remainder (normℂ inverse) (error · distance)
          (subst (_≤ℝ normℂ inverse) (sym (normℂ-neg inverse)) (≤ℝ-refl (normℂ inverse)))
          remainderBound)
        (subst (_≤ℝ q · distance) (sym (mulAssoc (normℂ inverse) error distance))
          (mulPres≤R-0≤ (normℂ inverse · error) q distance (normℂ-nonnegative (z -ℂ w)) inverseBound)))
    where
    distance : ℝ
    distance = normℂ (z -ℂ w)
    remainder : ℂ
    remainder = (pz -ℂ pw) -ℂ derivative ·ℂ (z -ℂ w)

  newtonCorrectionNorm : ∀ inverse center value →
    normℂ ((center -ℂ inverse ·ℂ value) -ℂ center) ≡ normℂ (inverse ·ℂ value)
  newtonCorrectionNorm inverse center value =
    cong normℂ (C.correction center inverse value) ∙ normℂ-neg (inverse ·ℂ value)
