module Cubical.Analysis.Complex.Modulus.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties using (subAddCancel; negSub)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue using (absℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition using (addReflects≤R)
open import Cubical.Analysis.Real.Order.AbsoluteValue using (absLeastUpperBound)
open import Cubical.Analysis.Real.Order.Strict.Properties using (≤<ℝ-trans)
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference using (absDifference<→closeness)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds
open import Cubical.Analysis.Complex.Modulus.Distance

private
  opaque
    directedModulusDifference : ∀ z w → modulusℂ z - modulusℂ w ≤ℝ distanceℂ z w
    directedModulusDifference z w = addReflects≤R (modulusℂ z - modulusℂ w) (distanceℂ z w) (modulusℂ w)
      (subst (_≤ℝ distanceℂ z w + modulusℂ w) (sym (subAddCancel (modulusℂ z) (modulusℂ w)))
        (subst (_≤ℝ distanceℂ z w + modulusℂ w) (cong modulusℂ (ℂRing.minusPlus z w))
          (modulusℂ-triangle (z -ℂ w) w)))

-- Reverse triangle inequality for the existing Euclidean modulus. The
-- product premetric still needs a factor of two in its input radius.
opaque
  modulusℂ-differenceBound : ∀ z w → absℝ (modulusℂ z - modulusℂ w) ≤ℝ distanceℂ z w
  modulusℂ-differenceBound z w = absLeastUpperBound (modulusℂ z - modulusℂ w) (distanceℂ z w)
    (directedModulusDifference z w)
    (subst2 _≤ℝ_ (sym (negSub (modulusℂ z) (modulusℂ w))) (distanceℂ-sym w z)
      (directedModulusDifference w z))

  modulusℂ-presCloseness : ∀ z w ε → z ∼ℂ[ ε /2₊ ] w → modulusℂ z ∼[ ε ] modulusℂ w
  modulusℂ-presCloseness z w ε close = absDifference<→closeness (modulusℂ z) (modulusℂ w) ε
    (≤<ℝ-trans (absℝ (modulusℂ z - modulusℂ w)) (distanceℂ z w) (rat (fst ε))
      (modulusℂ-differenceBound z w) (closeness→distanceℂ< z w ε close))

modulusℂ-isUniformlyContinuous : isUniformlyContinuous (ℂPremetricSpace .snd) modulusℂ (ℝPremetricSpace .snd)
modulusℂ-isUniformlyContinuous = ∣ (_/2₊) , record { pres≈ = modulusℂ-presCloseness } ∣₁

modulusℂ-isContinuous : isContinuous (ℂPremetricSpace .snd) modulusℂ (ℝPremetricSpace .snd)
modulusℂ-isContinuous = isUniformlyContinuous→isContinuous _ _ _ modulusℂ-isUniformlyContinuous
