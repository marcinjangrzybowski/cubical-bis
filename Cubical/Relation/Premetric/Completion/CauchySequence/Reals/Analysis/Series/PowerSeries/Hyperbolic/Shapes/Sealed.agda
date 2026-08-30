module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Shapes.Sealed where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Shapes


-- Prevent clients from normalizing through the reflected commutative-ring
-- certificates when these polynomial identities are specialized to reals.

opaque
  sinh-add-shape-sealed : ∀ {ℓ} (R : CommRing ℓ) →
    let open CommRingStr (snd R)
    in ∀ h a b c d →
      (h · h + h · h) · (a · c + (- (b · d)))
        ≡
      (h · (a + (- b))) · (h · (c + d)) +
        (h · (a + b)) · (h · (c + (- d)))
  sinh-add-shape-sealed R = HyperbolicAlgebra.sinh-add-shape R


  cosh-add-shape-sealed : ∀ {ℓ} (R : CommRing ℓ) →
    let open CommRingStr (snd R)
    in ∀ h a b c d →
      (h · h + h · h) · (a · c + b · d)
        ≡
      (h · (a + b)) · (h · (c + d)) +
        (h · (a + (- b))) · (h · (c + (- d)))
  cosh-add-shape-sealed R = HyperbolicAlgebra.cosh-add-shape R
