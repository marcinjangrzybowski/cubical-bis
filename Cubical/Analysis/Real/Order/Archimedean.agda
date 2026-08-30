module Cubical.Analysis.Real.Order.Archimedean where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Base as ℚBase
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚOrder
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚAbs
open import Cubical.Data.Rationals.Order.Floor using (boundℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚInstance
import Cubical.Algebra.OrderedCommRing.Properties as OrderedProperties

open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Algebra.Negation using (-_; neg-rat)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (negInvol)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue using (absℝ; abs-rat)
open import Cubical.Analysis.Real.Order.AbsoluteValue using (leAbs; negLeAbs)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational using (<ℚ→<ℝ)
open import Cubical.Analysis.Real.Order.Strict.Properties
  using (<ℝ-trans; ≤<ℝ-trans)
open import Cubical.Analysis.Real.Order.Strict.Addition using (<ℝ-neg)
open import Cubical.Analysis.Real.Order.RationalBounds
  using (∃rationalUpperBound)

private
  module ℚOrdered =
    OrderedProperties.OrderedCommRingTheory ℚInstance.ℚOrderedCommRing


naturalRational : ℕ₊₁ → ℚ
naturalRational n = [ ℤ.ℕ₊₁→ℤ n , 1 ]

naturalPositive : ∀ n → 0 ℚOrder.< naturalRational n
naturalPositive (1+ n) = ℚAbs.0<pos n 1

naturalBound : ℕ₊₁ → ℚInstance.PositiveRationals.ℚ₊
naturalBound n = naturalRational n , naturalPositive n

∃naturalUpperBound : ∀ x →
  ∃[ n ∈ ℕ₊₁ ] x <ℝ rat (naturalRational n)
∃naturalUpperBound x =
  PT.rec squash₁ fromRationalBound (∃rationalUpperBound x)
  where
  fromRationalBound :
    Σ[ q ∈ ℚ ] x <ℝ rat q →
    ∃[ n ∈ ℕ₊₁ ] x <ℝ rat (naturalRational n)
  fromRationalBound (q , x<q) =
    let
      n , absq<n = boundℕ q
      q<n : q ℚOrder.< naturalRational n
      q<n = ℚOrder.isTrans≤<
        q (ℚOrdered.abs q) (naturalRational n)
        (ℚOrdered.≤abs q) absq<n
    in
      ∣ n
      , <ℝ-trans x (rat q) (rat (naturalRational n))
          x<q (<ℚ→<ℝ q (naturalRational n) q<n)
      ∣₁

∃naturalLowerBound : ∀ x →
  ∃[ n ∈ ℕ₊₁ ] rat (ℚ.- naturalRational n) <ℝ x
∃naturalLowerBound x =
  PT.map lowerFromNegUpper (∃naturalUpperBound (- x))
  where
  lowerFromNegUpper :
    Σ[ n ∈ ℕ₊₁ ] (- x) <ℝ rat (naturalRational n) →
    Σ[ n ∈ ℕ₊₁ ] rat (ℚ.- naturalRational n) <ℝ x
  lowerFromNegUpper (n , -x<n) =
    n
    , subst2 _<ℝ_
        (neg-rat (naturalRational n))
        (negInvol x)
        (<ℝ-neg (- x) (rat (naturalRational n)) -x<n)

NaturalAbsBound : ℝ → Type₀
NaturalAbsBound x =
  Σ[ n ∈ ℕ₊₁ ] absℝ x <ℝ rat (naturalRational n)

∃naturalAbsBound : ∀ x → ∥ NaturalAbsBound x ∥₁
∃naturalAbsBound x = ∃naturalUpperBound (absℝ x)

rationalNaturalAbsBound : ∀ q → NaturalAbsBound (rat q)
rationalNaturalAbsBound q =
  let
    n , absq<n = boundℕ q
  in
    n
    , subst (_<ℝ rat (naturalRational n))
        (sym (abs-rat q))
        (<ℚ→<ℝ
          (ℚOrdered.abs q) (naturalRational n) absq<n)

NaturalTwoSidedBounds : ℝ → Type₀
NaturalTwoSidedBounds x =
  Σ[ n ∈ ℕ₊₁ ]
    (rat (ℚ.- naturalRational n) <ℝ x) ×
    (x <ℝ rat (naturalRational n))

∃naturalTwoSidedBounds : ∀ x → ∥ NaturalTwoSidedBounds x ∥₁
∃naturalTwoSidedBounds x =
  PT.map fromAbsBound (∃naturalAbsBound x)
  where
  fromAbsBound : NaturalAbsBound x → NaturalTwoSidedBounds x
  fromAbsBound (n , absx<n) =
    n
    , subst2 _<ℝ_
        (neg-rat (naturalRational n))
        (negInvol x)
        (<ℝ-neg (- x) (rat (naturalRational n))
          (≤<ℝ-trans
            (- x) (absℝ x) (rat (naturalRational n))
            (negLeAbs x) absx<n))
    , ≤<ℝ-trans
        x (absℝ x) (rat (naturalRational n))
        (leAbs x) absx<n
