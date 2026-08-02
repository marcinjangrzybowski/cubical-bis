module Cubical.HITs.CauchyRealsP.Algebra.Inverse.Bounded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Inverse using (_⁻¹₊)

open import Cubical.HITs.CauchyRealsP.Foundation

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Completion.Properties.Lift

import Cubical.Data.Rationals.Inverse as ℚInv

private
  module InverseExtension =
    LiftCompleteCodomain ℚPremetricSpace ℝPremetricSpace isCompleteℝ

reciprocalLipschitzBound : ℚ₊ → ℚ₊
reciprocalLipschitzBound η =
  (η ·₊ η) ⁻¹₊

clampedPositive : ℚ₊ → ℚ → ℚ₊
clampedPositive =
  ℚ.maxWithPos

boundedReciprocalℚ : ℚ₊ → ℚ → ℚ
boundedReciprocalℚ η q =
  fst ((clampedPositive η q) ⁻¹₊)

private
  boundedReciprocalDifference≤ : ∀ η q r →
    abs (boundedReciprocalℚ η q ℚ.- boundedReciprocalℚ η r)
      ℚ.≤
    fst (reciprocalLipschitzBound η) ℚ.· abs (q ℚ.- r)
  boundedReciprocalDifference≤ η q r =
    subst
      (ℚ._≤
        (fst (reciprocalLipschitzBound η) ℚ.· abs (q ℚ.- r)))
      (sym reciprocalDifferencePath)
      (ℚ.≤Monotone·-onNonNeg
        reciprocalFactor
        (fst (reciprocalLipschitzBound η))
        (abs
          (ℚ.max (fst η) r ℚ.-
           ℚ.max (fst η) q))
        (abs (q ℚ.- r))
        reciprocalFactor≤
        (subst
          (abs
            (ℚ.max (fst η) r ℚ.-
             ℚ.max (fst η) q) ℚ.≤_)
          (ℚOrder.abs-Comm r q)
          (ℚ.maxDist (fst η) q r))
        (ℚ.0≤ℚ₊
          ((clampedPositive η q ·₊
            clampedPositive η r) ⁻¹₊))
        (ℚOrder.0≤abs
          (ℚ.max (fst η) r ℚ.-
           ℚ.max (fst η) q)))
    where
    module ℚOrder =
      OrderedCommRingTheory ℚOrderedCommRing

    reciprocalFactor : ℚ
    reciprocalFactor =
      fst
        ((clampedPositive η q ·₊
          clampedPositive η r) ⁻¹₊)

    reciprocalFactor≤ :
      reciprocalFactor
        ℚ.≤ fst (reciprocalLipschitzBound η)
    reciprocalFactor≤ =
      ℚInv.invℚ₊≤invℚ₊
        (clampedPositive η q ·₊ clampedPositive η r)
        (η ·₊ η)
        (ℚ.≤Monotone·-onNonNeg
          (fst η)
          (ℚ.max (fst η) q)
          (fst η)
          (ℚ.max (fst η) r)
          (ℚ.≤max (fst η) q)
          (ℚ.≤max (fst η) r)
          (ℚ.0≤ℚ₊ η)
          (ℚ.0≤ℚ₊ η))

    reciprocalDifferencePath :
      abs
        (boundedReciprocalℚ η q ℚ.-
         boundedReciprocalℚ η r)
      ≡
      reciprocalFactor ℚ.·
        abs
          (ℚ.max (fst η) r ℚ.-
           ℚ.max (fst η) q)
    reciprocalDifferencePath =
      cong abs
        (ℚInv.1/p+1/q
          (clampedPositive η q)
          (clampedPositive η r))
      ∙ ℚ.pos·abs
          reciprocalFactor
          (ℚ.max (fst η) r ℚ.-
           ℚ.max (fst η) q)
          (ℚ.0≤ℚ₊
            ((clampedPositive η q ·₊
              clampedPositive η r) ⁻¹₊))

boundedReciprocalLip : ∀ η →
  IsLipschitzWith
    (snd ℚPremetricSpace)
    (λ q → rat (boundedReciprocalℚ η q))
    (snd ℝPremetricSpace)
    (reciprocalLipschitzBound η)
boundedReciprocalLip η
  .IsLipschitzWith.pres≈ q r ε q∼r =
    rat-rat
      (boundedReciprocalℚ η q)
      (boundedReciprocalℚ η r)
      (reciprocalLipschitzBound η ·₊ ε)
      (ℚ.isTrans≤<
        (abs
          (boundedReciprocalℚ η q ℚ.-
           boundedReciprocalℚ η r))
        (fst (reciprocalLipschitzBound η) ℚ.·
         abs (q ℚ.- r))
        (fst (reciprocalLipschitzBound η) ℚ.·
         fst ε)
        (boundedReciprocalDifference≤ η q r)
        (ℚ.<-o·
          (abs (q ℚ.- r))
          (fst ε)
          (fst (reciprocalLipschitzBound η))
          (snd (reciprocalLipschitzBound η))
          q∼r))

boundedReciprocalExtension : ∀ η →
  Σ[ f ∈ (ℝ → ℝ) ]
  IsLipschitzWith
    (snd ℝPremetricSpace) f
    (snd ℝPremetricSpace)
    (reciprocalLipschitzBound η)
boundedReciprocalExtension η =
  InverseExtension.liftLipschitzWith
    (reciprocalLipschitzBound η)
    (λ q → rat (boundedReciprocalℚ η q))
    (boundedReciprocalLip η)

boundedReciprocalℝ : ℚ₊ → ℝ → ℝ
boundedReciprocalℝ η =
  fst (boundedReciprocalExtension η)

boundedReciprocalIsLipschitz : ∀ η →
  IsLipschitzWith
    (snd ℝPremetricSpace)
    (boundedReciprocalℝ η)
    (snd ℝPremetricSpace)
    (reciprocalLipschitzBound η)
boundedReciprocalIsLipschitz η =
  snd (boundedReciprocalExtension η)

boundedReciprocal-rat : ∀ η q →
  boundedReciprocalℝ η (rat q) ≡
  rat (boundedReciprocalℚ η q)
boundedReciprocal-rat η q =
  refl

boundedReciprocalℚAbove : ∀ η q →
  (0<q : 0 ℚ.< q) →
  fst η ℚ.≤ q →
  boundedReciprocalℚ η q ≡
  fst ((q , 0<q) ⁻¹₊)
boundedReciprocalℚAbove η q 0<q η≤q =
  cong (fst ∘ _⁻¹₊)
    (ℚ₊≡
      (ℚ.≤→max (fst η) q η≤q))
