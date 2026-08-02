module Cubical.HITs.CauchyRealsP.Algebra.Order.Density where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Metric

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

denseℚinℝ : ∀ x y →
  x <ℝ y → ∃[ q ∈ ℚ ] (x <ℝ rat q) × (rat q <ℝ y)
denseℚinℝ x y =
  PT.rec squash₁ proveFromGap
  where
  proveFromGap :
    PositiveGap x y →
    ∃[ q ∈ ℚ ] (x <ℝ rat q) × (rat q <ℝ y)
  proveFromGap w =
    PT.map betweenFromApproximation (∃ratApprox x α)
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
        (ℚ.+Comm (fst (δ /2₊)) (fst α)
        ∙ cong (fst α ℚ.+_)
            (sym (1/2∈ℚ./4+/4≡/2 (fst δ))))
        (1/2∈ℚ./2+/2≡id (fst δ))
        (ℚ.<-o+
          (fst α) (fst (δ /2₊)) (fst (δ /2₊))
          (/4₊</2₊ δ))

    x+δ≤y : x + rat (fst δ) ≤ℝ y
    x+δ≤y = gapBoundElim x y δ (bound w)

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

      p+α<q : p ℚ.+ fst α ℚ.< q
      p+α<q =
        subst2 ℚ._<_
          (ℚ.+IdL (p ℚ.+ fst α))
          (ℚ.+Comm (fst α) (p ℚ.+ fst α)
          ∙ sym (ℚ.+Assoc p (fst α) (fst α)))
          (ℚ.<-+o
            0 (fst α) (p ℚ.+ fst α) (snd α))

      x<q : x <ℝ rat q
      x<q =
        ≤<ℝ-trans
          x (rat (p ℚ.+ fst α)) (rat q)
          x≤p+α
          (<ℚ→<ℝ (p ℚ.+ fst α) q p+α<q)

      p≤x+α : rat p ≤ℝ x + rat (fst α)
      p≤x+α =
        close→upperBound (rat p) x α ratp∼x

      q≤x+α+twoα :
        rat q ≤ℝ (x + rat (fst α)) + rat (fst twoα)
      q≤x+α+twoα =
        subst
          (_≤ℝ ((x + rat (fst α)) + rat (fst twoα)))
          (rat+rat p (fst twoα))
          (≤ℝ-addR
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
        <≤ℝ-trans
          (rat q) (x + rat (fst δ)) y
          (≤<ℝ-trans
            (rat q)
            ((x + rat (fst α)) + rat (fst twoα))
            (x + rat (fst δ))
            q≤x+α+twoα
            x+α+twoα<x+δ)
          x+δ≤y
