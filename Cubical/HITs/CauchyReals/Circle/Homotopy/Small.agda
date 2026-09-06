module Cubical.HITs.CauchyReals.Circle.Homotopy.Small where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.UniformGroup
open import Cubical.HITs.CauchyReals.Circle.Winding
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Base
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Algebra
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Quotient
open import Cubical.HITs.CauchyReals.Circle.Homotopy.LocalLift
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Lifted
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

-- Maps landing in this closed strip of the right half-circle contract
-- through the bounded angle furnished by LocalLift.
strip-null : (f : CircleMap) →
  (∀ x → 0 <ᵣ fst (fst (Circle→distCircle (fst f x)))) →
  (∀ x → absᵣ (snd (fst (Circle→distCircle (fst f x)))) ≤ᵣ rat [ 1 / 2 ]) →
  Homotopic f zeroCircleMap
strip-null f positive bound = lifted-null f logarithm 1 bounded lifts
  where
  logarithm : UC[ CirclePremetricSpace , ℝPremetricSpace ]
  logarithm = localAngleUC ∘UC (circleYCoordinateUC ∘UC (Circle→distCircleUC ∘UC f))
  bounded : ∀ x → absᵣ (fst logarithm x) ≤ᵣ 1
  bounded x = <ᵣWeaken≤ᵣ _ _ (isTrans<ᵣ _ (rat [ 1 / 4 ]) 1
    (localAngle-bound (Circle→distCircle (fst f x)) (positive x) (bound x)) decℚ<ᵣ?)
  lifts : ∀ x → injCircle (fst logarithm x) ≡ fst f x
  lifts x = circle-image-injective _ _ (sym (cover-β (fst logarithm x))
    ∙ localAngle-cover (Circle→distCircle (fst f x)) (positive x) (bound x))

private
  module D = PremetricStr (snd distCirclePremetricSpace)
  module C = PremetricStr (snd CirclePremetricSpace)
  module Q = AbGroupStr (snd CircleHomotopyAbGroup)
  module QG = GroupTheory (AbGroup→Group CircleHomotopyAbGroup)

  half-close-strip : (p : distCircle) → p D.≈[ [ 1 / 2 ]₊ ] circle0 →
    (0 <ᵣ fst (fst p)) × (absᵣ (snd (fst p)) ≤ᵣ rat [ 1 / 2 ])
  half-close-strip ((x , y) , norm) close = positive , <ᵣWeaken≤ᵣ _ _ small-y
    where
    x-close : absᵣ (x -ᵣ 1) <ᵣ rat [ 1 / 2 ]
    x-close = equivFun (∼≃abs<ε x 1 ([ 1 / 2 ]₊))
      (≈ℝ→∼ x 1 ([ 1 / 2 ]₊) (fst close))
    positive : 0 <ᵣ x
    positive = isTrans<ᵣ 0 (rat [ 1 / 2 ]) x decℚ<ᵣ?
      (subst2 _<ᵣ_ ℝ! ℝ!
        (<ᵣ-+o _ _ 1 (fst (abs<→ointerval (x -ᵣ 1) (rat [ 1 / 2 ]) x-close))))
    small-y : absᵣ y <ᵣ rat [ 1 / 2 ]
    small-y = isTrans≡<ᵣ _ _ _ (cong absᵣ ℝ!)
      (equivFun (∼≃abs<ε y 0 ([ 1 / 2 ]₊))
        (≈ℝ→∼ y 0 ([ 1 / 2 ]₊) (snd close)))

  opaque
    close-difference : (p q r : distCircle) → r ≡ p ℝS¹.+ (ℝS¹.- q) →
      p D.≈[ circleAddModulus ([ 1 / 2 ]₊) ] q → r D.≈[ [ 1 / 2 ]₊ ] circle0
    close-difference p q r image close = subst2 (λ a b → a D.≈[ [ 1 / 2 ]₊ ] b)
      (sym image) (ℝS¹.+InvR q)
      (circle-add-close p (ℝS¹.- q) q (ℝS¹.- q) ([ 1 / 2 ]₊) close
        (D.isRefl≈ (ℝS¹.- q) (circleAddModulus ([ 1 / 2 ]₊))))

-- One radius works for every pair of uniformly continuous circle maps.
-- This proves existence of a genuine uniform homotopy, not only equality
-- of their winding numbers.
close-homotopic : (f g : CircleMap) →
  (∀ x → fst f x C.≈[ circleAddModulus ([ 1 / 2 ]₊) ] fst g x) → Homotopic f g
close-homotopic f g close = class-effective f g
  (QG.·CancelR (negClass (class g))
    (SQ.eq/ _ _ (strip-null difference (λ x → fst (strip x)) (λ x → snd (strip x)))
      ∙ sym (Q.+InvR (class g))))
  where
  difference : CircleMap
  difference = addCircleUC f (negCircleUC g)
  image : ∀ x → Circle→distCircle (fst difference x) ≡
    Circle→distCircle (fst f x) ℝS¹.+ (ℝS¹.- Circle→distCircle (fst g x))
  image x = addCircle-image f (negCircleUC g) x
    ∙ cong (Circle→distCircle (fst f x) ℝS¹.+_) (negCircle-image g x)
  close-zero : ∀ x → Circle→distCircle (fst difference x) D.≈[ [ 1 / 2 ]₊ ] circle0
  close-zero x = close-difference (Circle→distCircle (fst f x))
    (Circle→distCircle (fst g x)) (Circle→distCircle (fst difference x)) (image x) (close x)
  strip : ∀ x → (0 <ᵣ fst (fst (Circle→distCircle (fst difference x)))) ×
    (absᵣ (snd (fst (Circle→distCircle (fst difference x)))) ≤ᵣ rat [ 1 / 2 ])
  strip x = half-close-strip (Circle→distCircle (fst difference x)) (close-zero x)
