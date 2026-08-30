module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Shapes.Real where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Shapes


IdentityShapesAt : CommRing ℓ-zero → Type
IdentityShapesAt R =
  IdentityShapes (fst R)
    (CommRingStr._+_ (snd R))
    (CommRingStr._·_ (snd R))
    (CommRingStr.-_ (snd R))


opaque
  identityShapes-sealed : IdentityShapesAt sealedℝCommRing
  identityShapes-sealed = identityShapes sealedℝCommRing

  identityShapes-real-structure : IdentityShapesAt ℝCommRing
  identityShapes-real-structure =
    subst IdentityShapesAt sealedℝCommRing-agrees identityShapes-sealed

  identityShapes-real-add :
    IdentityShapes Real.ℝ Add._+_
      (CommRingStr._·_ (snd ℝCommRing))
      (CommRingStr.-_ (snd ℝCommRing))
  identityShapes-real-add =
    subst
      (λ add → IdentityShapes Real.ℝ add
        (CommRingStr._·_ (snd ℝCommRing))
        (CommRingStr.-_ (snd ℝCommRing)))
      ℝCommRing-add-agrees identityShapes-real-structure

  identityShapes-real-mul :
    IdentityShapes Real.ℝ Add._+_ Mul._·_
      (CommRingStr.-_ (snd ℝCommRing))
  identityShapes-real-mul =
    subst
      (λ mul → IdentityShapes Real.ℝ Add._+_ mul
        (CommRingStr.-_ (snd ℝCommRing)))
      ℝCommRing-mul-agrees identityShapes-real-add

  realIdentityShapes :
    IdentityShapes Real.ℝ Add._+_ Mul._·_ Neg.-_
  realIdentityShapes =
    subst (IdentityShapes Real.ℝ Add._+_ Mul._·_)
      ℝCommRing-neg-agrees identityShapes-real-mul


open IdentityShapes realIdentityShapes public
  renaming
    ( negative-product to negative-product-real
    ; add-removed-square to add-removed-square-real
    ; remove-difference to remove-difference-real
    ; sinh-sub-shape to sinh-sub-shape-real
    ; cosh-sub-shape to cosh-sub-shape-real
    ; sinh-double-shape to sinh-double-shape-real
    ; one-plus-double-sine-shape to one-plus-double-sine-shape-real
    ; double-cosine-minus-one-shape to double-cosine-minus-one-shape-real
    ; cosh-sum-shape to cosh-sum-shape-real
    ; cosh-difference-shape to cosh-difference-shape-real
    ; sinh-sum-shape to sinh-sum-shape-real
    ; sinh-difference-shape to sinh-difference-shape-real
    )
