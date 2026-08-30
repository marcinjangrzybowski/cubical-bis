module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Clamp
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (close→upperBound)


ClosedAbsRadiusPredicate : Real.ℝ → ℙ Real.ℝ
ClosedAbsRadiusPredicate radius x =
  (Abs.absℝ x ≤ℝ radius)
  , isProp≤ℝ (Abs.absℝ x) radius


OpenAbsRadiusPredicate : Real.ℝ → ℙ Real.ℝ
OpenAbsRadiusPredicate radius x =
  (Abs.absℝ x <ℝ radius)
  , isProp<ℝ (Abs.absℝ x) radius


ClosedAbsRadius : Real.ℝ → Type₀
ClosedAbsRadius radius =
  Σ[ x ∈ Real.ℝ ] x ∈ ClosedAbsRadiusPredicate radius


ClosedAbsRadiusPremetricSpace :
  Real.ℝ → PremetricSpace ℓ-zero ℓ-zero
ClosedAbsRadiusPremetricSpace radius =
  PremetricSubspace Real.ℝPremetricSpace
    (ClosedAbsRadiusPredicate radius)


closedAbsRadiusInclusionNE : ∀ radius →
  NE[ ClosedAbsRadiusPremetricSpace radius , Real.ℝPremetricSpace ]
closedAbsRadiusInclusionNE radius =
  subspaceInclusionNE Real.ℝPremetricSpace
    (ClosedAbsRadiusPredicate radius)


closedAbsRadiusRetractionNE : ∀ radius →
  Real.ιℚ 0 ≤ℝ radius →
  NE[ Real.ℝPremetricSpace , ClosedAbsRadiusPremetricSpace radius ]
fst (closedAbsRadiusRetractionNE radius 0≤radius) x =
  clampInterval (Neg.- radius) radius x
  , clampSymmetricAbsBound radius 0≤radius x
IsNonExpanding.pres≈
  (snd (closedAbsRadiusRetractionNE radius 0≤radius))
  x y ε =
  clampInterval-pres≈ (Neg.- radius) radius x y ε


closedAbsRadiusRetractionSection : ∀ radius →
  (0≤radius : Real.ιℚ 0 ≤ℝ radius) → ∀ point →
  fst (closedAbsRadiusRetractionNE radius 0≤radius)
      (fst (closedAbsRadiusInclusionNE radius) point) ≡ point
closedAbsRadiusRetractionSection radius 0≤radius point =
  Σ≡Prop
    (λ x → isProp≤ℝ (Abs.absℝ x) radius)
    (clampSymmetricFixpointFromAbs radius (fst point) (snd point))


closedAbsRadiusCoordinateIsContinuous : ∀ radius →
  isContinuous
    (snd (ClosedAbsRadiusPremetricSpace radius)) fst
    (snd Real.ℝPremetricSpace)
closedAbsRadiusCoordinateIsContinuous radius =
  snd (NE→C (closedAbsRadiusInclusionNE radius))


-- Openness is proved directly from a strict-gap witness.  The gap is opened
-- only while constructing the propositionally truncated neighbourhood; no
-- radius is extracted from the open-membership proposition.

openAbsRadiusIsOpen : ∀ radius →
  IsOpenPredicate
    (snd Real.ℝPremetricSpace)
    (OpenAbsRadiusPredicate radius)
openAbsRadiusIsOpen radius x interior =
  PT.map neighbourhood interior
  where
  neighbourhood :
    PositiveGap (Abs.absℝ x) radius →
    Σ[ δ ∈ ℚ₊ ]
      (∀ y → x Real.Base.≈ᶜ[ δ ] y →
        Abs.absℝ y <ℝ radius)
  neighbourhood gap =
    width gap /2₊ , λ y x≈y →
      ∣ positiveGap (width gap /2₊)
          (≤ℝ-trans
            (Abs.absℝ y Add.+ Real.ιℚ (fst (width gap /2₊)))
            ((Abs.absℝ x Add.+ Real.ιℚ (fst (width gap /2₊)))
              Add.+ Real.ιℚ (fst (width gap /2₊)))
            radius
            (add-preserves≤-right
              (Abs.absℝ y)
              (Abs.absℝ x Add.+ Real.ιℚ (fst (width gap /2₊)))
              (Real.ιℚ (fst (width gap /2₊)))
              (close→upperBound
                (Abs.absℝ y) (Abs.absℝ x) (width gap /2₊)
                (Real.Base.sym≈ᶜ
                  (Abs.absℝ x) (Abs.absℝ y) (width gap /2₊)
                  (Abs.absℝ-pres≈ x y (width gap /2₊) x≈y))))
            (subst (_≤ℝ radius)
              (sym
                (sym
                  (add-assoc
                    (Abs.absℝ x)
                    (Real.ιℚ (fst (width gap /2₊)))
                    (Real.ιℚ (fst (width gap /2₊))))
                ∙ cong (Abs.absℝ x Add.+_)
                  (Add.add-ι-ι
                    (fst (width gap /2₊))
                    (fst (width gap /2₊))
                  ∙ cong Real.ιℚ
                      (/2+/2≡id (fst (width gap))))))
              (bound gap))) ∣₁


openAbsRadius⊆closedAbsRadius : ∀ radius →
  OpenAbsRadiusPredicate radius ⊆ ClosedAbsRadiusPredicate radius
openAbsRadius⊆closedAbsRadius radius x interior =
  <ℝ-weaken (Abs.absℝ x) radius interior
