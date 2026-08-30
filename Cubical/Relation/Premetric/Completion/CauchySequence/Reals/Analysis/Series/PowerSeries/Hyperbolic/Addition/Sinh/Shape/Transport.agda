module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Addition.Sinh.Shape.Transport where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Shapes.Sealed


SinhAdditionShape : CommRing ℓ-zero → Type
SinhAdditionShape R =
  let open CommRingStr (snd R)
  in ∀ h a b c d →
    (h · h + h · h) · (a · c + (- (b · d)))
      ≡
    (h · (a + (- b))) · (h · (c + d)) +
      (h · (a + b)) · (h · (c + (- d)))


SinhAdditionOperations :
  (Real.ℝ → Real.ℝ → Real.ℝ) →
  (Real.ℝ → Real.ℝ → Real.ℝ) →
  (Real.ℝ → Real.ℝ) → Type
SinhAdditionOperations add mul neg = ∀ h a b c d →
  mul (add (mul h h) (mul h h))
      (add (mul a c) (neg (mul b d)))
    ≡
  add
    (mul (mul h (add a (neg b))) (mul h (add c d)))
    (mul (mul h (add a b)) (mul h (add c (neg d))))


opaque
  sinh-add-shape-at-sealed : SinhAdditionShape sealedℝCommRing
  sinh-add-shape-at-sealed = sinh-add-shape-sealed sealedℝCommRing


  sinh-add-shape-at-real : SinhAdditionShape ℝCommRing
  sinh-add-shape-at-real =
    subst SinhAdditionShape
      sealedℝCommRing-agrees
      sinh-add-shape-at-sealed


  sinh-add-shape-at-real-operations :
    SinhAdditionOperations
      (CommRingStr._+_ (snd ℝCommRing))
      (CommRingStr._·_ (snd ℝCommRing))
      (CommRingStr.-_ (snd ℝCommRing))
  sinh-add-shape-at-real-operations = sinh-add-shape-at-real


  sinh-add-shape-concrete-add :
    SinhAdditionOperations
      Add._+_
      (CommRingStr._·_ (snd ℝCommRing))
      (CommRingStr.-_ (snd ℝCommRing))
  sinh-add-shape-concrete-add =
    subst
      (λ add → SinhAdditionOperations add
        (CommRingStr._·_ (snd ℝCommRing))
        (CommRingStr.-_ (snd ℝCommRing)))
      ℝCommRing-add-agrees
      sinh-add-shape-at-real-operations


  sinh-add-shape-concrete-mul :
    SinhAdditionOperations
      Add._+_
      Mul._·_
      (CommRingStr.-_ (snd ℝCommRing))
  sinh-add-shape-concrete-mul =
    subst
      (λ mul → SinhAdditionOperations Add._+_ mul
        (CommRingStr.-_ (snd ℝCommRing)))
      ℝCommRing-mul-agrees
      sinh-add-shape-concrete-add


  sinh-add-shape-concrete :
    SinhAdditionOperations Add._+_ Mul._·_ Neg.-_
  sinh-add-shape-concrete =
    subst
      (SinhAdditionOperations Add._+_ Mul._·_)
      ℝCommRing-neg-agrees
      sinh-add-shape-concrete-mul
