module Cubical.HITs.CauchyRealsP.Algebra.Order.RationalBounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Metric

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

RationalInterval : ℝ → ℚ₊ → Type
RationalInterval x ε =
  Σ[ q ∈ ℚ ]
    (rat (q ℚ.- fst ε) ≤ℝ x) ×
    (x ≤ℝ rat (q ℚ.+ fst ε))

rationalInterval : ∀ x ε → ∥ RationalInterval x ε ∥₁
rationalInterval x ε =
  PT.map intervalFromApproximation (∃ratApprox x ε)
  where
  intervalFromApproximation :
    Σ[ q ∈ ℚ ] rat q ∼[ ε ] x →
    RationalInterval x ε
  intervalFromApproximation (q , ratq∼x) =
    q
    , subst (_≤ℝ x)
        (sub-rat q (fst ε))
        (close→lowerBound x (rat q) ε
          (sym∼ (rat q) x ε ratq∼x))
    , subst (x ≤ℝ_)
        (rat+rat q (fst ε))
        (close→upperBound x (rat q) ε
          (sym∼ (rat q) x ε ratq∼x))

StrictRationalBounds : ℝ → Type
StrictRationalBounds x =
  Σ[ q ∈ ℚ ] Σ[ r ∈ ℚ ]
    (rat q <ℝ x) × (x <ℝ rat r)

strictRationalBoundsAt : ∀ x ε → ∥ StrictRationalBounds x ∥₁
strictRationalBoundsAt x ε =
  PT.map widen (rationalInterval x ε)
  where
  widen : RationalInterval x ε → StrictRationalBounds x
  widen (p , lower≤x , x≤upper) =
    qLower , qUpper
    , <≤ℝ-trans
        (rat qLower) (rat (p ℚ.- fst ε)) x
        (<ℚ→<ℝ qLower (p ℚ.- fst ε) lower<near)
        lower≤x
    , ≤<ℝ-trans
        x (rat (p ℚ.+ fst ε)) (rat qUpper)
        x≤upper
        (<ℚ→<ℝ (p ℚ.+ fst ε) qUpper near<upper)
    where
    qLower : ℚ
    qLower = p ℚ.- (fst ε ℚ.+ fst ε)

    qUpper : ℚ
    qUpper = p ℚ.+ (fst ε ℚ.+ fst ε)

    lower<near : qLower ℚ.< p ℚ.- fst ε
    lower<near =
      subst2 ℚ._<_ ℚ! ℚ!
        (ℚ.<-+o 0 (fst ε) qLower (snd ε))

    near<upper : p ℚ.+ fst ε ℚ.< qUpper
    near<upper =
      subst2 ℚ._<_ ℚ! ℚ!
        (ℚ.<-+o 0 (fst ε) (p ℚ.+ fst ε) (snd ε))

strictRationalBounds : ∀ x → ∥ StrictRationalBounds x ∥₁
strictRationalBounds x = strictRationalBoundsAt x [ 1 / 1 ]₊

∃rationalLowerBound : ∀ x → ∃[ q ∈ ℚ ] rat q <ℝ x
∃rationalLowerBound x =
  PT.map (λ (q , _ , q<x , _) → q , q<x)
    (strictRationalBounds x)

∃rationalUpperBound : ∀ x → ∃[ q ∈ ℚ ] x <ℝ rat q
∃rationalUpperBound x =
  PT.map (λ (_ , q , _ , x<q) → q , x<q)
    (strictRationalBounds x)
