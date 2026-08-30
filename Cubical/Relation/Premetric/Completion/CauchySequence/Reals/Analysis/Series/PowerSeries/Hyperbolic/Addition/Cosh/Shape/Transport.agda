module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Addition.Cosh.Shape.Transport where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Shapes.Sealed

CoshAdditionShape : CommRing ℓ-zero → Type
CoshAdditionShape R =
  let open CommRingStr (snd R)
  in ∀ h a b c d →
    (h · h + h · h) · (a · c + b · d)
      ≡
    (h · (a + b)) · (h · (c + d)) +
      (h · (a + (- b))) · (h · (c + (- d)))

CoshAdditionOperations :
  (Real.ℝ → Real.ℝ → Real.ℝ) →
  (Real.ℝ → Real.ℝ → Real.ℝ) →
  (Real.ℝ → Real.ℝ) → Type
CoshAdditionOperations add mul neg = ∀ h a b c d →
  mul (add (mul h h) (mul h h)) (add (mul a c) (mul b d))
    ≡
  add
    (mul (mul h (add a b)) (mul h (add c d)))
    (mul (mul h (add a (neg b))) (mul h (add c (neg d))))

opaque
  cosh-add-shape-at-sealed : CoshAdditionShape sealedℝCommRing
  cosh-add-shape-at-sealed = cosh-add-shape-sealed sealedℝCommRing

  cosh-add-shape-at-real : CoshAdditionShape ℝCommRing
  cosh-add-shape-at-real =
    subst CoshAdditionShape sealedℝCommRing-agrees
      cosh-add-shape-at-sealed

  cosh-add-shape-at-real-operations :
    CoshAdditionOperations
      (CommRingStr._+_ (snd ℝCommRing))
      (CommRingStr._·_ (snd ℝCommRing))
      (CommRingStr.-_ (snd ℝCommRing))
  cosh-add-shape-at-real-operations = cosh-add-shape-at-real

  cosh-add-shape-concrete-add :
    CoshAdditionOperations Add._+_
      (CommRingStr._·_ (snd ℝCommRing))
      (CommRingStr.-_ (snd ℝCommRing))
  cosh-add-shape-concrete-add =
    subst
      (λ add → CoshAdditionOperations add
        (CommRingStr._·_ (snd ℝCommRing))
        (CommRingStr.-_ (snd ℝCommRing)))
      ℝCommRing-add-agrees cosh-add-shape-at-real-operations

  cosh-add-shape-concrete-mul :
    CoshAdditionOperations Add._+_ Mul._·_
      (CommRingStr.-_ (snd ℝCommRing))
  cosh-add-shape-concrete-mul =
    subst
      (λ mul → CoshAdditionOperations Add._+_ mul
        (CommRingStr.-_ (snd ℝCommRing)))
      ℝCommRing-mul-agrees cosh-add-shape-concrete-add

  cosh-add-shape-concrete :
    CoshAdditionOperations Add._+_ Mul._·_ Neg.-_
  cosh-add-shape-concrete =
    subst (CoshAdditionOperations Add._+_ Mul._·_)
      ℝCommRing-neg-agrees cosh-add-shape-concrete-mul
