module Cubical.Analysis.Real.Order.RationalBounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚInstance
open import Cubical.Data.Rationals.Base as ℚBase
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚOrder

open import Cubical.Analysis.Real.Base
  using (ℝ; rat; _∼[_]_; rat-dense; sym∼)
open import Cubical.Analysis.Real.Algebra.Addition using (rat+rat)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
  using (sub-rat)
open import Cubical.Analysis.Real.Order.Base using (_≤ℝ_)
open import Cubical.Analysis.Real.Order.Metric
  using (close→lowerBound; close→upperBound)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational using (<ℚ→<ℝ)
open import Cubical.Analysis.Real.Order.Strict.Properties
  using (≤<ℝ-trans; <≤ℝ-trans)

open ℚInstance.PositiveRationals using (ℚ₊; [_/_]₊)


RationalInterval : ℝ → ℚ₊ → Type₀
RationalInterval x ε =
  Σ[ q ∈ ℚ ]
    (rat (q ℚ.- fst ε) ≤ℝ x) ×
    (x ≤ℝ rat (q ℚ.+ fst ε))

rationalInterval : ∀ x ε → ∥ RationalInterval x ε ∥₁
rationalInterval x ε =
  PT.map intervalFromApproximation (rat-dense x ε)
  where
  intervalFromApproximation :
    Σ[ q ∈ ℚ ] rat q ∼[ ε ] x → RationalInterval x ε
  intervalFromApproximation (q , ratq∼x) =
    q
    , subst (_≤ℝ x) (sub-rat q (fst ε))
        (close→lowerBound x (rat q) ε
          (sym∼ (rat q) x ε ratq∼x))
    , subst (x ≤ℝ_) (rat+rat q (fst ε))
        (close→upperBound x (rat q) ε
          (sym∼ (rat q) x ε ratq∼x))

StrictRationalBounds : ℝ → Type₀
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
        (rat qLower) (rat nearLower) x
        (<ℚ→<ℝ qLower nearLower lower<near) lower≤x
    , ≤<ℝ-trans
        x (rat nearUpper) (rat qUpper)
        x≤upper (<ℚ→<ℝ nearUpper qUpper near<upper)
    where
    e : ℚ
    e = fst ε

    nearLower : ℚ
    nearLower = p ℚ.- e

    nearUpper : ℚ
    nearUpper = p ℚ.+ e

    qLower : ℚ
    qLower = nearLower ℚ.- e

    qUpper : ℚ
    qUpper = nearUpper ℚ.+ e

    lowerCancel : qLower ℚ.+ e ≡ nearLower
    lowerCancel =
      sym (ℚ.+Assoc nearLower (ℚ.- e) e)
      ∙ cong (nearLower ℚ.+_) (ℚ.+InvL e)
      ∙ ℚ.+IdR nearLower

    lower<near : qLower ℚOrder.< nearLower
    lower<near = subst2 ℚOrder._<_
      (ℚ.+IdR qLower) lowerCancel
      (ℚOrder.<-o+ 0 e qLower (snd ε))

    near<upper : nearUpper ℚOrder.< qUpper
    near<upper = subst (λ u → u ℚOrder.< qUpper)
      (ℚ.+IdR nearUpper)
      (ℚOrder.<-o+ 0 e nearUpper (snd ε))

strictRationalBounds : ∀ x → ∥ StrictRationalBounds x ∥₁
strictRationalBounds x = strictRationalBoundsAt x [ 1 / 1 ]₊

∃rationalLowerBound : ∀ x →
  ∃[ q ∈ ℚ ] rat q <ℝ x
∃rationalLowerBound x =
  PT.map (λ (q , _ , q<x , _) → q , q<x)
    (strictRationalBounds x)

∃rationalUpperBound : ∀ x →
  ∃[ q ∈ ℚ ] x <ℝ rat q
∃rationalUpperBound x =
  PT.map (λ (_ , q , _ , x<q) → q , x<q)
    (strictRationalBounds x)
