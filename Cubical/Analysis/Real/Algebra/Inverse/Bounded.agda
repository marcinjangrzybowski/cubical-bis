module Cubical.Analysis.Real.Algebra.Inverse.Bounded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚR
open import Cubical.Data.Rationals.Inverse using (_⁻¹₊)
import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.Data.Rationals.Order
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Rationals.Order.Algebra

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals using
  (ℚPremetricSpace)

open import Cubical.Analysis.Real.Base
import Cubical.Analysis.Completion.Lipschitz as LipschitzDefinition

open PositiveRationals
open OrderedCommRingTheory ℚOrderedCommRing


module ℚ where
  open import Cubical.Data.Rationals.Base public
  open import Cubical.Data.Rationals.Properties public
  open import Cubical.Data.Rationals.Order public
  open import Cubical.Data.Rationals.Order.AbsoluteValue public
  open import Cubical.Data.Rationals.Order.Algebra public


private
  module Extension =
    LipschitzDefinition ℚPremetricSpace ℚPremetricSpace


reciprocalLipschitzBound : ℚ₊ → ℚ₊
reciprocalLipschitzBound η = (η ·₊ η) ⁻¹₊


clampedPositive : ℚ₊ → ℚ → ℚ₊
clampedPositive = ℚ.maxWithPos


boundedReciprocalℚ : ℚ₊ → ℚ → ℚ
boundedReciprocalℚ η q = fst ((clampedPositive η q) ⁻¹₊)


private
  boundedReciprocalDifference≤ : ∀ η q r →
    abs (boundedReciprocalℚ η q ℚR.- boundedReciprocalℚ η r)
      ℚ.≤
    fst (reciprocalLipschitzBound η) ℚR.· abs (q ℚR.- r)
  boundedReciprocalDifference≤ η q r =
    subst
      (ℚ._≤
        (fst (reciprocalLipschitzBound η) ℚR.· abs (q ℚR.- r)))
      (sym reciprocalDifferencePath)
      (ℚ.≤Monotone·-onNonNeg
        reciprocalFactor
        (fst (reciprocalLipschitzBound η))
        (abs
          (ℚ.max (fst η) r ℚR.-
           ℚ.max (fst η) q))
        (abs (q ℚR.- r))
        reciprocalFactor≤
        (subst
          (abs
            (ℚ.max (fst η) r ℚR.-
             ℚ.max (fst η) q) ℚ.≤_)
          (abs-Comm r q)
          (ℚ.maxDist (fst η) q r))
        (ℚ.0≤ℚ₊
          ((clampedPositive η q ·₊
            clampedPositive η r) ⁻¹₊))
        (0≤abs
          (ℚ.max (fst η) r ℚR.-
           ℚ.max (fst η) q)))
    where
    reciprocalFactor : ℚ
    reciprocalFactor =
      fst
        ((clampedPositive η q ·₊
          clampedPositive η r) ⁻¹₊)

    reciprocalFactor≤ :
      reciprocalFactor ℚ.≤ fst (reciprocalLipschitzBound η)
    reciprocalFactor≤ =
      ℚInv.invℚ₊≤invℚ₊
        (clampedPositive η q ·₊ clampedPositive η r)
        (η ·₊ η)
        (ℚ.≤Monotone·-onNonNeg
          (fst η) (ℚ.max (fst η) q)
          (fst η) (ℚ.max (fst η) r)
          (ℚ.≤max (fst η) q)
          (ℚ.≤max (fst η) r)
          (ℚ.0≤ℚ₊ η) (ℚ.0≤ℚ₊ η))

    reciprocalDifferencePath :
      abs
        (boundedReciprocalℚ η q ℚR.- boundedReciprocalℚ η r)
      ≡
      reciprocalFactor ℚR.·
        abs (ℚ.max (fst η) r ℚR.- ℚ.max (fst η) q)
    reciprocalDifferencePath =
      cong abs
        (ℚInv.1/p+1/q
          (clampedPositive η q) (clampedPositive η r))
      ∙ ℚ.pos·abs
          reciprocalFactor
          (ℚ.max (fst η) r ℚR.- ℚ.max (fst η) q)
          (ℚ.0≤ℚ₊
            ((clampedPositive η q ·₊ clampedPositive η r) ⁻¹₊))


boundedReciprocalIsLipschitzℚ : ∀ η →
  IsLipschitzWith
    (ℚPremetricSpace .snd) (boundedReciprocalℚ η)
    (ℚPremetricSpace .snd) (reciprocalLipschitzBound η)
boundedReciprocalIsLipschitzℚ η
  .IsLipschitzWith.pres≈ q r ε q∼r =
    ℚ.isTrans≤<
      (abs (boundedReciprocalℚ η q ℚR.- boundedReciprocalℚ η r))
      (fst (reciprocalLipschitzBound η) ℚR.· abs (q ℚR.- r))
      (fst (reciprocalLipschitzBound η) ℚR.· fst ε)
      (boundedReciprocalDifference≤ η q r)
      (ℚ.<-o·
        (abs (q ℚR.- r)) (fst ε)
        (fst (reciprocalLipschitzBound η))
        (snd (reciprocalLipschitzBound η)) q∼r)


boundedReciprocalExtension : ∀ η →
  Σ[ f ∈ (ℝ → ℝ) ]
    IsLipschitzWith
      (ℝPremetricSpace .snd) f
      (ℝPremetricSpace .snd) (reciprocalLipschitzBound η)
boundedReciprocalExtension η =
  Extension.liftLipschitzWith
    (reciprocalLipschitzBound η)
    (boundedReciprocalℚ η)
    (boundedReciprocalIsLipschitzℚ η)


boundedReciprocalℝ : ℚ₊ → ℝ → ℝ
boundedReciprocalℝ η = fst (boundedReciprocalExtension η)


boundedReciprocalIsLipschitz : ∀ η →
  IsLipschitzWith
    (ℝPremetricSpace .snd) (boundedReciprocalℝ η)
    (ℝPremetricSpace .snd) (reciprocalLipschitzBound η)
boundedReciprocalIsLipschitz η = snd (boundedReciprocalExtension η)


boundedReciprocal-rat : ∀ η q →
  boundedReciprocalℝ η (rat q) ≡
  rat (boundedReciprocalℚ η q)
boundedReciprocal-rat η q =
  Extension.liftLipschitzWith-ι
    (reciprocalLipschitzBound η)
    (boundedReciprocalℚ η)
    (boundedReciprocalIsLipschitzℚ η) q


boundedReciprocalℚAbove : ∀ η q →
  (0<q : 0 ℚ.< q) → fst η ℚ.≤ q →
  boundedReciprocalℚ η q ≡ fst ((q , 0<q) ⁻¹₊)
boundedReciprocalℚAbove η q 0<q η≤q =
  cong (fst ∘ _⁻¹₊)
    (ℚ₊≡ (ℚ.≤→max (fst η) q η≤q))
