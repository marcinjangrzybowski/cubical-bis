module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Density where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚData
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ


-- Metric density plus the rational-centred order bounds gives genuine order
-- density.  All approximation choices remain propositionally truncated.

denseℚinℝ : ∀ x y →
  x <ℝ y → ∃[ q ∈ ℚData.ℚ ] (x <ℝ Real.ιℚ q) × (Real.ιℚ q <ℝ y)
denseℚinℝ x y = PT.rec squash₁ proveFromGap
  where
  proveFromGap : PositiveGap x y →
    ∃[ q ∈ ℚData.ℚ ] (x <ℝ Real.ιℚ q) × (Real.ιℚ q <ℝ y)
  proveFromGap w = PT.map betweenFromApproximation (Real.rationalsDense x α)
    where
    δ : ℚ₊
    δ = width w

    α : ℚ₊
    α = δ /4₊

    twoα : ℚ₊
    twoα = α +₊ α

    threeα<δ : (α +₊ twoα) <₊ δ
    threeα<δ =
      subst2 ℚ._<_
        (ℚData.+Comm (fst (δ /2₊)) (fst α)
        ∙ cong (fst α ℚData.+_)
            (sym (/4+/4≡/2 (fst δ))))
        (/2+/2≡id (fst δ))
        (ℚ.<-o+
          (fst α) (fst (δ /2₊)) (fst (δ /2₊))
          (/4₊</2₊ δ))

    x+δ≤y : x Add.+ Real.ιℚ (fst δ) ≤ℝ y
    x+δ≤y = bound w

    betweenFromApproximation :
      Σ[ p ∈ ℚData.ℚ ] (Real.ιℚ p Real.Base.≈ᶜ[ α ] x) →
      Σ[ q ∈ ℚData.ℚ ] (x <ℝ Real.ιℚ q) × (Real.ιℚ q <ℝ y)
    betweenFromApproximation (p , ιp∼x) = q , x≪q , q≪y
      where
      q : ℚData.ℚ
      q = p ℚData.+ fst twoα

      x≤p+α : x ≤ℝ Real.ιℚ (p ℚData.+ fst α)
      x≤p+α = rationalClose→lowerBound p x α ιp∼x

      p+α<q : p ℚData.+ fst α ℚ.< q
      p+α<q =
        subst2 ℚ._<_
          (ℚData.+IdL (p ℚData.+ fst α))
          (ℚData.+Comm (fst α) (p ℚData.+ fst α)
          ∙ sym (ℚData.+Assoc p (fst α) (fst α)))
          (ℚ.<-+o
            0 (fst α) (p ℚData.+ fst α) (snd α))

      x≪q : x <ℝ Real.ιℚ q
      x≪q =
        ≤<ℝ-trans x (Real.ιℚ (p ℚData.+ fst α)) (Real.ιℚ q)
          x≤p+α (<ℚ→<ℝ (p ℚData.+ fst α) q p+α<q)

      p≤x+α : Real.ιℚ p ≤ℝ (x Add.+ Real.ιℚ (fst α))
      p≤x+α = rationalClose→upperBound p x α ιp∼x

      q≤x+α+twoα :
        Real.ιℚ q ≤ℝ
          ((x Add.+ Real.ιℚ (fst α)) Add.+ Real.ιℚ (fst twoα))
      q≤x+α+twoα =
        subst
          (_≤ℝ ((x Add.+ Real.ιℚ (fst α)) Add.+ Real.ιℚ (fst twoα)))
          (Add.add-ι-ι p (fst twoα))
          (add-preserves≤-right
            (Real.ιℚ p) (x Add.+ Real.ιℚ (fst α))
            (Real.ιℚ (fst twoα)) p≤x+α)

      x+α+twoα≪x+δ :
        ((x Add.+ Real.ιℚ (fst α)) Add.+ Real.ιℚ (fst twoα))
          <ℝ (x Add.+ Real.ιℚ (fst δ))
      x+α+twoα≪x+δ =
        subst2 _<ℝ_ leftPath refl
          (<ℝ-add-left
            (Real.ιℚ (fst α ℚData.+ fst twoα))
            (Real.ιℚ (fst δ)) x
            (<ℚ→<ℝ (fst α ℚData.+ fst twoα) (fst δ) threeα<δ))
        where
        leftPath :
          x Add.+ Real.ιℚ (fst α ℚData.+ fst twoα) ≡
          (x Add.+ Real.ιℚ (fst α)) Add.+ Real.ιℚ (fst twoα)
        leftPath =
            cong (x Add.+_) (sym (Add.add-ι-ι (fst α) (fst twoα)))
          ∙ add-assoc x (Real.ιℚ (fst α)) (Real.ιℚ (fst twoα))

      q≪y : Real.ιℚ q <ℝ y
      q≪y =
        ≪≤ℝ-trans (Real.ιℚ q) (x Add.+ Real.ιℚ (fst δ)) y
          (≤<ℝ-trans
            (Real.ιℚ q)
            ((x Add.+ Real.ιℚ (fst α)) Add.+ Real.ιℚ (fst twoα))
            (x Add.+ Real.ιℚ (fst δ))
            q≤x+α+twoα x+α+twoα≪x+δ)
          x+δ≤y
