module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Shapes where

open import Cubical.Foundations.Prelude
open import Cubical.Tactics.CommRingSolver
open import Cubical.Algebra.CommRing


module IdentityAlgebra {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)

  opaque
    negative-product : ∀ cosine sine →
      cosine · cosine + sine · (- sine)
        ≡ cosine · cosine - sine · sine
    negative-product cosine sine = solve! R

    add-removed-square : ∀ cosine sine →
      cosine · cosine
        ≡ (cosine · cosine - sine · sine) + sine · sine
    add-removed-square cosine sine = solve! R

    remove-difference : ∀ cosine sine →
      sine · sine
        ≡ cosine · cosine -
          (cosine · cosine - sine · sine)
    remove-difference cosine sine = solve! R

    sinh-sub-shape : ∀ sx sy cx cy →
      sx · cy + cx · (- sy) ≡ sx · cy - cx · sy
    sinh-sub-shape sx sy cx cy = solve! R

    cosh-sub-shape : ∀ sx sy cx cy →
      cx · cy + sx · (- sy) ≡ cx · cy - sx · sy
    cosh-sub-shape sx sy cx cy = solve! R

    sinh-double-shape : ∀ sine cosine →
      sine · cosine + cosine · sine
        ≡ sine · cosine + sine · cosine
    sinh-double-shape sine cosine = solve! R

    one-plus-double-sine-shape : ∀ cosine sine →
      cosine · cosine + sine · sine
        ≡ (cosine · cosine - sine · sine) +
          (sine · sine + sine · sine)
    one-plus-double-sine-shape cosine sine = solve! R

    double-cosine-minus-one-shape : ∀ cosine sine →
      cosine · cosine + sine · sine
        ≡ (cosine · cosine + cosine · cosine) -
          (cosine · cosine - sine · sine)
    double-cosine-minus-one-shape cosine sine = solve! R

    cosh-sum-shape : ∀ cx cy sx sy →
      (cx · cy + sx · sy) + (cx · cy - sx · sy)
        ≡ cx · cy + cx · cy
    cosh-sum-shape cx cy sx sy = solve! R

    cosh-difference-shape : ∀ cx cy sx sy →
      (cx · cy + sx · sy) - (cx · cy - sx · sy)
        ≡ sx · sy + sx · sy
    cosh-difference-shape cx cy sx sy = solve! R

    sinh-sum-shape : ∀ sx sy cx cy →
      (sx · cy + cx · sy) + (sx · cy - cx · sy)
        ≡ sx · cy + sx · cy
    sinh-sum-shape sx sy cx cy = solve! R

    sinh-difference-shape : ∀ sx sy cx cy →
      (sx · cy + cx · sy) - (sx · cy - cx · sy)
        ≡ cx · sy + cx · sy
    sinh-difference-shape sx sy cx cy = solve! R


record IdentityShapes {ℓ} (A : Type ℓ)
    (add mul : A → A → A) (neg : A → A) : Type ℓ where
  field
    negative-product : ∀ cosine sine →
      add (mul cosine cosine) (mul sine (neg sine))
        ≡ add (mul cosine cosine) (neg (mul sine sine))

    add-removed-square : ∀ cosine sine →
      mul cosine cosine
        ≡ add (add (mul cosine cosine) (neg (mul sine sine)))
            (mul sine sine)

    remove-difference : ∀ cosine sine →
      mul sine sine
        ≡ add (mul cosine cosine)
            (neg (add (mul cosine cosine) (neg (mul sine sine))))

    sinh-sub-shape : ∀ sx sy cx cy →
      add (mul sx cy) (mul cx (neg sy))
        ≡ add (mul sx cy) (neg (mul cx sy))

    cosh-sub-shape : ∀ sx sy cx cy →
      add (mul cx cy) (mul sx (neg sy))
        ≡ add (mul cx cy) (neg (mul sx sy))

    sinh-double-shape : ∀ sine cosine →
      add (mul sine cosine) (mul cosine sine)
        ≡ add (mul sine cosine) (mul sine cosine)

    one-plus-double-sine-shape : ∀ cosine sine →
      add (mul cosine cosine) (mul sine sine)
        ≡ add (add (mul cosine cosine) (neg (mul sine sine)))
            (add (mul sine sine) (mul sine sine))

    double-cosine-minus-one-shape : ∀ cosine sine →
      add (mul cosine cosine) (mul sine sine)
        ≡ add (add (mul cosine cosine) (mul cosine cosine))
            (neg (add (mul cosine cosine) (neg (mul sine sine))))

    cosh-sum-shape : ∀ cx cy sx sy →
      add (add (mul cx cy) (mul sx sy))
          (add (mul cx cy) (neg (mul sx sy)))
        ≡ add (mul cx cy) (mul cx cy)

    cosh-difference-shape : ∀ cx cy sx sy →
      add (add (mul cx cy) (mul sx sy))
          (neg (add (mul cx cy) (neg (mul sx sy))))
        ≡ add (mul sx sy) (mul sx sy)

    sinh-sum-shape : ∀ sx sy cx cy →
      add (add (mul sx cy) (mul cx sy))
          (add (mul sx cy) (neg (mul cx sy)))
        ≡ add (mul sx cy) (mul sx cy)

    sinh-difference-shape : ∀ sx sy cx cy →
      add (add (mul sx cy) (mul cx sy))
          (neg (add (mul sx cy) (neg (mul cx sy))))
        ≡ add (mul cx sy) (mul cx sy)


identityShapes : ∀ {ℓ} (R : CommRing ℓ) →
  IdentityShapes (fst R)
    (CommRingStr._+_ (snd R))
    (CommRingStr._·_ (snd R))
    (CommRingStr.-_ (snd R))
identityShapes R = record
  { negative-product = IdentityAlgebra.negative-product R
  ; add-removed-square = IdentityAlgebra.add-removed-square R
  ; remove-difference = IdentityAlgebra.remove-difference R
  ; sinh-sub-shape = IdentityAlgebra.sinh-sub-shape R
  ; cosh-sub-shape = IdentityAlgebra.cosh-sub-shape R
  ; sinh-double-shape = IdentityAlgebra.sinh-double-shape R
  ; one-plus-double-sine-shape = IdentityAlgebra.one-plus-double-sine-shape R
  ; double-cosine-minus-one-shape = IdentityAlgebra.double-cosine-minus-one-shape R
  ; cosh-sum-shape = IdentityAlgebra.cosh-sum-shape R
  ; cosh-difference-shape = IdentityAlgebra.cosh-difference-shape R
  ; sinh-sum-shape = IdentityAlgebra.sinh-sum-shape R
  ; sinh-difference-shape = IdentityAlgebra.sinh-difference-shape R
  }
