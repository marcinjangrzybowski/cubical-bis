module Cubical.Analysis.Complex.Polynomial.Bounds.Step where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
import Cubical.Analysis.Complex.Algebra.Identities as IdentitiesDefinition

private module C = IdentitiesDefinition.Identities ℂCommRing

opaque
  hornerBoundℂ : ∀ a z p radius bound → normℂ z ≤ℝ radius → normℂ p ≤ℝ bound →
    normℂ (a +ℂ z ·ℂ p) ≤ℝ normℂ a + radius · bound
  hornerBoundℂ a z p radius bound zb pb =
    normℂ-addBound a (z ·ℂ p) (normℂ a) (radius · bound)
      (≤ℝ-refl (normℂ a)) (normℂ-mulBound z p radius bound zb pb)

  hornerLipschitzℂ : ∀ a z w p s radius bound lip →
    normℂ w ≤ℝ radius → normℂ p ≤ℝ bound →
    normℂ (p -ℂ s) ≤ℝ lip · normℂ (z -ℂ w) →
    normℂ ((a +ℂ z ·ℂ p) -ℂ (a +ℂ w ·ℂ s)) ≤ℝ
      (bound + radius · lip) · normℂ (z -ℂ w)
  hornerLipschitzℂ a z w p s radius bound lip wb pb db =
    subst2 _≤ℝ_ (sym (cong normℂ (C.hornerDifference a z w p s)))
      (cong₂ _+_ (mulComm distance bound) (mulAssoc radius lip distance)
        ∙ sym (mulDistL bound (radius · lip) distance))
      (normℂ-addBound ((z -ℂ w) ·ℂ p) (w ·ℂ (p -ℂ s))
        (distance · bound) (radius · (lip · distance))
        (normℂ-mulBound (z -ℂ w) p distance bound (≤ℝ-refl distance) pb)
        (normℂ-mulBound w (p -ℂ s) radius (lip · distance) wb db))
    where
    distance : ℝ
    distance = normℂ (z -ℂ w)
