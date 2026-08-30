module Cubical.Analysis.Real.Order.Strict.Density where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚInstance
open import Cubical.Data.Rationals.Base as ℚBase
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚOrder

open import Cubical.Analysis.Real.Base
  using (ℝ; rat; _∼[_]_; rat-dense; sym∼)
open import Cubical.Analysis.Real.Algebra.Addition using (_+_; rat+rat)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (addAssoc)
open import Cubical.Analysis.Real.Order.Base
  using (_≤ℝ_; ≤ℝ-trans; rat≤rat≃)
open import Cubical.Analysis.Real.Order.Addition
  using (addPres≤R)
open import Cubical.Analysis.Real.Order.Metric using (close→upperBound)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational using (<ℚ→<ℝ)
open import Cubical.Analysis.Real.Order.Strict.Properties
  using (≤<ℝ-trans; <≤ℝ-trans)
open import Cubical.Analysis.Real.Order.Strict.Addition using (<ℝ-addL)

open ℚInstance.PositiveRationals using (ℚ₊; _+₊_)
open ℚInstance.PositiveRationals.PositiveHalvesℚ
  using (_/2₊; _/4₊; /4₊</2₊)


denseℚinℝ : ∀ x y →
  x <ℝ y → ∃[ q ∈ ℚ ] (x <ℝ rat q) × (rat q <ℝ y)
denseℚinℝ x y = PT.rec squash₁ proveFromGap
  where
  proveFromGap :
    PositiveGap x y →
    ∃[ q ∈ ℚ ] (x <ℝ rat q) × (rat q <ℝ y)
  proveFromGap (δ , x+δ≤y) =
    PT.map betweenFromApproximation (rat-dense x α)
    where
    α : ℚ₊
    α = δ /4₊

    twoα : ℚ₊
    twoα = α +₊ α

    threeα<δ : fst (α +₊ twoα) ℚOrder.< fst δ
    threeα<δ =
      subst2 ℚOrder._<_
        (ℚ.+Comm (fst (δ /2₊)) (fst α)
        ∙ cong (fst α ℚ.+_)
            (sym (ℚInstance.1/2∈ℚ./4+/4≡/2 (fst δ))))
        (ℚInstance.1/2∈ℚ./2+/2≡id (fst δ))
        (ℚOrder.<-o+
          (fst α) (fst (δ /2₊)) (fst (δ /2₊))
          (/4₊</2₊ δ))

    betweenFromApproximation :
      Σ[ p ∈ ℚ ] rat p ∼[ α ] x →
      Σ[ q ∈ ℚ ] (x <ℝ rat q) × (rat q <ℝ y)
    betweenFromApproximation (p , ratp∼x) =
      q , x<q , q<y
      where
      q : ℚ
      q = p ℚ.+ fst twoα

      x≤p+α : x ≤ℝ rat (p ℚ.+ fst α)
      x≤p+α =
        subst (x ≤ℝ_)
          (rat+rat p (fst α))
          (close→upperBound x (rat p) α
            (sym∼ (rat p) x α ratp∼x))

      p+α<q : p ℚ.+ fst α ℚOrder.< q
      p+α<q =
        subst2 ℚOrder._<_
          (ℚ.+IdL (p ℚ.+ fst α))
          (ℚ.+Comm (fst α) (p ℚ.+ fst α)
          ∙ sym (ℚ.+Assoc p (fst α) (fst α)))
          (ℚOrder.<-+o
            0 (fst α) (p ℚ.+ fst α) (snd α))

      x<q : x <ℝ rat q
      x<q = ≤<ℝ-trans x (rat (p ℚ.+ fst α)) (rat q)
        x≤p+α (<ℚ→<ℝ (p ℚ.+ fst α) q p+α<q)

      p≤x+α : rat p ≤ℝ x + rat (fst α)
      p≤x+α = close→upperBound (rat p) x α ratp∼x

      q≤x+α+twoα :
        rat q ≤ℝ (x + rat (fst α)) + rat (fst twoα)
      q≤x+α+twoα =
        subst
          (_≤ℝ ((x + rat (fst α)) + rat (fst twoα)))
          (rat+rat p (fst twoα))
          (addPres≤R
            (rat p) (x + rat (fst α))
            (rat (fst twoα)) p≤x+α)

      x+α+twoα<x+δ :
        (x + rat (fst α)) + rat (fst twoα)
          <ℝ x + rat (fst δ)
      x+α+twoα<x+δ =
        subst
          (_<ℝ x + rat (fst δ))
          (addAssoc x (rat (fst α)) (rat (fst twoα)))
          (<ℝ-addL
            (rat (fst α) + rat (fst twoα))
            (rat (fst δ)) x
            (subst
              (_<ℝ rat (fst δ))
              (rat+rat (fst α) (fst twoα))
              (<ℚ→<ℝ
                (fst α ℚ.+ fst twoα) (fst δ)
                threeα<δ)))

      q<y : rat q <ℝ y
      q<y =
        <≤ℝ-trans (rat q) (x + rat (fst δ)) y
          (≤<ℝ-trans
            (rat q)
            ((x + rat (fst α)) + rat (fst twoα))
            (x + rat (fst δ))
            q≤x+α+twoα x+α+twoα<x+δ)
          x+δ≤y
