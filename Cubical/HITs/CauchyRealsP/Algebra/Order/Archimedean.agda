module Cubical.HITs.CauchyRealsP.Algebra.Order.Archimedean where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Order.Floor
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyRealsP.Algebra.Order.RationalBounds

naturalRational : ℕ₊₁ → ℚ
naturalRational n = [ ℤ.ℕ₊₁→ℤ n , 1 ]

naturalPositive : ∀ n → 0 ℚ.< naturalRational n
naturalPositive (1+ n) = ℚ.0<pos n 1

naturalBound : ℕ₊₁ → ℚ₊
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
      q<n : q ℚ.< naturalRational n
      q<n =
        ℚ.isTrans≤<
          q (abs q) (naturalRational n)
          (OrderedCommRingTheory.≤abs ℚOrderedCommRing q)
          absq<n
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

NaturalAbsBound : ℝ → Type
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
    , subst
        (_<ℝ rat (naturalRational n))
        (sym (abs-rat q))
        (<ℚ→<ℝ
          (abs q) (naturalRational n) absq<n)

NaturalTwoSidedBounds : ℝ → Type
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
