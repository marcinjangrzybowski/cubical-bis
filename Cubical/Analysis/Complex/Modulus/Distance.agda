module Cubical.Analysis.Complex.Modulus.Distance where

-- Euclidean distance and explicit conversion from coordinate closeness.
-- A quarter-radius in each endpoint controls their distance by one radius;
-- the factors of two are not hidden by identifying the two metrics.

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.CommRing using (ℝCommRing)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Norm using (normℂ)
open import Cubical.Analysis.Complex.Norm.Metric
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds
import Cubical.Analysis.Complex.Modulus.DistanceAlgebra as Algebra

private
  module C = Algebra.DistanceAlgebra ℂCommRing
  module R = Algebra.DistanceAlgebra ℝCommRing

distanceℂ : ℂ → ℂ → ℝ
distanceℂ z w = modulusℂ (z -ℂ w)

distanceℂ-refl : ∀ z → distanceℂ z z ≡ 0ℝ
distanceℂ-refl z = cong modulusℂ (+ℂInvR z) ∙ modulusℂ-zero

distanceℂ-sym : ∀ z w → distanceℂ z w ≡ distanceℂ w z
distanceℂ-sym z w = cong modulusℂ (C.difference-opposite z w) ∙ modulusℂ-neg (w -ℂ z)

opaque
  distanceℂ-triangle : ∀ a b c → distanceℂ a c ≤ℝ distanceℂ a b + distanceℂ b c
  distanceℂ-triangle a b c = subst (_≤ℝ distanceℂ a b + distanceℂ b c)
    (sym (cong modulusℂ (C.difference-chain a b c)))
    (modulusℂ-triangle (a -ℂ b) (b -ℂ c))

  closeness→distanceℂ< : ∀ z w (ε : ℚ₊) → z ∼ℂ[ ε /2₊ ] w →
    distanceℂ z w <ℝ rat (fst ε)
  closeness→distanceℂ< z w ε close = subst (distanceℂ z w <ℝ_)
    (rat+rat (fst (ε /2₊)) (fst (ε /2₊)) ∙ cong rat (1/2∈ℚ./2+/2≡id (fst ε)))
    (≤<ℝ-trans (distanceℂ z w) (normℂ (z -ℂ w))
      (rat (fst (ε /2₊)) + rat (fst (ε /2₊)))
      (modulusℂ≤normℂ (z -ℂ w)) (closeness→normℂ-difference< z w (ε /2₊) close))

  distanceℂ-perturb< : ∀ a b c d (ε : ℚ₊) →
    a ∼ℂ[ (ε /2₊) /2₊ ] c → b ∼ℂ[ (ε /2₊) /2₊ ] d →
    distanceℂ a b <ℝ distanceℂ c d + rat (fst ε)
  distanceℂ-perturb< a b c d ε ac bd = ≤<ℝ-trans
    (distanceℂ a b) (distanceℂ c d + (distanceℂ a c + distanceℂ d b))
    (distanceℂ c d + rat (fst ε)) bound
    (<ℝ-addL (distanceℂ a c + distanceℂ d b) (rat (fst ε)) (distanceℂ c d) error)
    where
    bound : distanceℂ a b ≤ℝ distanceℂ c d + (distanceℂ a c + distanceℂ d b)
    bound = subst (distanceℂ a b ≤ℝ_)
      (R.middle-first (distanceℂ a c) (distanceℂ c d) (distanceℂ d b))
      (≤ℝ-trans (distanceℂ a b) (distanceℂ a c + distanceℂ c b)
        (distanceℂ a c + (distanceℂ c d + distanceℂ d b))
        (distanceℂ-triangle a c b)
        (addPres≤L (distanceℂ c b) (distanceℂ c d + distanceℂ d b) (distanceℂ a c)
          (distanceℂ-triangle c d b)))

    error : distanceℂ a c + distanceℂ d b <ℝ rat (fst ε)
    error = subst (distanceℂ a c + distanceℂ d b <ℝ_)
      (rat+rat (fst (ε /2₊)) (fst (ε /2₊)) ∙ cong rat (1/2∈ℚ./2+/2≡id (fst ε)))
      (<ℝ-add (distanceℂ a c) (rat (fst (ε /2₊)))
        (distanceℂ d b) (rat (fst (ε /2₊)))
        (closeness→distanceℂ< a c (ε /2₊) ac)
        (closeness→distanceℂ< d b (ε /2₊) (sym∼ℂ b d ((ε /2₊) /2₊) bd)))
