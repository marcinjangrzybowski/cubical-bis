module Cubical.Analysis.Real.Domain.OpenRadius where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.HITs.PropositionalTruncation as PT

import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚInstance
open ℚInstance.PositiveRationals using (ℚ₊)
open ℚInstance.PositiveRationals.PositiveHalvesℚ using (_/2₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Metric
open import Cubical.Analysis.Real.Order.Strict.Base

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace


OpenAbsRadiusPredicate : ℝ → ℙ ℝ
OpenAbsRadiusPredicate radius x =
  (absℝ x <ℝ radius)
  , isProp<ℝ (absℝ x) radius

isPropOpenAbsRadiusMembership : ∀ radius x →
  isProp (x ∈ OpenAbsRadiusPredicate radius)
isPropOpenAbsRadiusMembership radius x =
  isProp<ℝ (absℝ x) radius

OpenAbsRadius : ℝ → Type₀
OpenAbsRadius radius =
  Σ[ x ∈ ℝ ] x ∈ OpenAbsRadiusPredicate radius

isSetOpenAbsRadius : ∀ radius →
  isSet (OpenAbsRadius radius)
isSetOpenAbsRadius radius =
  isSetΣSndProp isSetℝ (isPropOpenAbsRadiusMembership radius)

OpenAbsRadiusPremetricSpace :
  ℝ → PremetricSpace ℓ-zero ℓ-zero
OpenAbsRadiusPremetricSpace radius =
  PremetricSubspace ℝPremetricSpace (OpenAbsRadiusPredicate radius)


openAbsRadiusInclusionNE : ∀ radius →
  NE[ OpenAbsRadiusPremetricSpace radius , ℝPremetricSpace ]
openAbsRadiusInclusionNE radius =
  subspaceInclusionNE ℝPremetricSpace (OpenAbsRadiusPredicate radius)

openAbsRadiusInclusionUC : ∀ radius →
  UC[ OpenAbsRadiusPremetricSpace radius , ℝPremetricSpace ]
openAbsRadiusInclusionUC radius =
  NE→UC (openAbsRadiusInclusionNE radius)

openAbsRadiusInclusionC : ∀ radius →
  C[ OpenAbsRadiusPremetricSpace radius , ℝPremetricSpace ]
openAbsRadiusInclusionC radius =
  NE→C (openAbsRadiusInclusionNE radius)


-- A strict gap `abs x + δ ≤ radius` leaves a half-gap neighbourhood
-- around x.  Pattern matching on the gap keeps its endpoints explicit and
-- avoids normalising projections through the completion implementation.

opaque
  openAbsRadiusIsOpen : ∀ radius →
    IsOpenPredicate
      (ℝPremetricSpace .snd)
      (OpenAbsRadiusPredicate radius)
  openAbsRadiusIsOpen radius x =
    PT.map (neighbourhood radius x)
    where
    neighbourhood : ∀ radius x →
      PositiveGap (absℝ x) radius →
      Σ[ ε ∈ ℚ₊ ]
        (∀ y → x ∼[ ε ] y → absℝ y <ℝ radius)
    neighbourhood radius x (δ , absx+δ≤radius) =
      δ /2₊ , λ y x∼y →
        ∣ δ /2₊
        , ≤ℝ-trans
            (absℝ y + half)
            ((absℝ x + half) + half)
            radius
            (addPres≤R
              (absℝ y) (absℝ x + half) half
              (close→upperBound
                (absℝ y) (absℝ x) (δ /2₊)
                (sym∼
                  (absℝ x) (absℝ y) (δ /2₊)
                  (abs-pres∼ x y (δ /2₊) x∼y))))
            (subst (_≤ℝ radius)
              (sym doubleHalfPath)
              absx+δ≤radius)
        ∣₁
      where
      half : ℝ
      half = rat (fst (δ /2₊))

      doubleHalfPath :
        (absℝ x + half) + half ≡
        absℝ x + rat (fst δ)
      doubleHalfPath =
        sym (addAssoc (absℝ x) half half)
        ∙ cong (absℝ x +_)
            (rat+rat (fst (δ /2₊)) (fst (δ /2₊))
            ∙ cong rat
                (ℚInstance.1/2∈ℚ./2+/2≡id (fst δ)))
