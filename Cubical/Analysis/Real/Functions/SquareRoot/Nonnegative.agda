module Cubical.Analysis.Real.Functions.SquareRoot.Nonnegative where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals.Base using (ℚ; [_/_]; fromNatℚ)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Sequence
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Functions.SquareRoot.Order
open import Cubical.Analysis.Real.Functions.SquareRoot.Positive
open import Cubical.Analysis.Real.Functions.SquareRoot.Estimates
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Geometric
open import Cubical.Analysis.Real.Series.Geometric.Real

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  halfℚ : ℚ
  halfℚ = [ pos 1 / 1+ 1 ]

  half = rat halfℚ

  half-positive : 0ℝ <ℝ half
  half-positive = <ℚ→<ℝ 0 halfℚ (ℚ.pos<pos tt)

  half-small : half <ℝ 1ℝ
  half-small = <ℚ→<ℝ halfℚ 1 (ℚ.pos<pos tt)

  half-nonnegative : 0ℝ ≤ℝ half
  half-nonnegative = <ℝ-weaken 0ℝ half half-positive

  radius : ℕ → ℝ
  radius = powℝ half

  radius-positive : ∀ n → 0ℝ <ℝ radius n
  radius-positive zero = <ℚ→<ℝ 0 1 (ℚ.pos<pos tt)
  radius-positive (suc n) = mulPositive half (radius n) half-positive (radius-positive n)

  radius-nonnegative : ∀ n → 0ℝ ≤ℝ radius n
  radius-nonnegative n = powNonnegative half n half-nonnegative

  radius-decreases : ∀ n → radius (suc n) ≤ℝ radius n
  radius-decreases n = subst (radius (suc n) ≤ℝ_) (mulIdL (radius n))
    (mulPres≤R-0≤ half 1ℝ (radius n) (radius-nonnegative n)
      (<ℝ-weaken half 1ℝ half-small))

  radius-limit : isLimitSequence radius 0ℝ
  radius-limit = realGeometricPowersTendToZero half
    (subst (_<ℝ 1ℝ) (sym (absOfNonnegative half half-nonnegative)) half-small)

-- These approximants are specified by a formula, not selected from a
-- radiuswise existence theorem. Their successive errors have a geometric
-- bound, so the native completion accepts them without countable choice.
module Approximation (x : ℝ) (nonnegative : 0ℝ ≤ℝ x) where
  private
    shifted : ℕ → ℝ
    shifted n = x + radius n · radius n

    shifted-positive : ∀ n → 0ℝ <ℝ shifted n
    shifted-positive n = subst (_<ℝ shifted n) (addIdL 0ℝ)
      (≤<ℝ-add 0ℝ x 0ℝ (radius n · radius n) nonnegative
        (mulPositive (radius n) (radius n) (radius-positive n) (radius-positive n)))

  points : ℕ → ℝ
  points n = positiveSqrtℝ (shifted n) (shifted-positive n)

  points-nonnegative : ∀ n → 0ℝ ≤ℝ points n
  points-nonnegative n = <ℝ-weaken 0ℝ (points n)
    (positiveSqrtℝ-positive (shifted n) (shifted-positive n))

  points-square : ∀ n → points n · points n ≡ shifted n
  points-square n = positiveSqrtℝ-square (shifted n) (shifted-positive n)

  private
    points-decrease : ∀ n → points (suc n) ≤ℝ points n
    points-decrease n = squareReflects≤Nonnegative (points (suc n)) (points n)
      (points-nonnegative n)
      (subst2 _≤ℝ_ (sym (points-square (suc n))) (sym (points-square n))
        (addPres≤L (radius (suc n) · radius (suc n)) (radius n · radius n) x
          (mulPres≤ (radius (suc n)) (radius n) (radius (suc n)) (radius n)
            (radius-nonnegative n) (radius-nonnegative (suc n))
            (radius-decreases n) (radius-decreases n))))

    increment-bound : ∀ n → absℝ (successiveIncrements points n) ≤ℝ 1ℝ · radius n
    increment-bound n = subst (absℝ (successiveIncrements points n) ≤ℝ_)
      (sym (mulIdL (radius n)))
      (nonnegativeSquareDifferenceBound (points n) (points (suc n)) (radius n)
        (points-nonnegative (suc n)) (points-decrease n) (radius-nonnegative n)
        (subst2 _≤ℝ_ (sym (points-square n))
          (cong (_+ radius n · radius n) (sym (points-square (suc n))))
          (addPres≤R x (shifted (suc n)) (radius n · radius n)
            (subst (_≤ℝ shifted (suc n)) (addIdR x)
              (addPres≤L 0ℝ (radius (suc n) · radius (suc n)) x
                (<ℝ-weaken 0ℝ (radius (suc n) · radius (suc n))
                  (mulPositive (radius (suc n)) (radius (suc n))
                    (radius-positive (suc n)) (radius-positive (suc n)))))))))

  points-cauchy : SeqWitness points
  points-cauchy = geometricallyBoundedIncrementsCauchy points half 1ℝ
    half-nonnegative half-small increment-bound

  opaque
    value : ℝ
    value = limitOfSequence points points-cauchy

    value-limit : isLimitSequence points value
    value-limit = limitOfSequenceIsLimit points points-cauchy

  value-nonnegative : 0ℝ ≤ℝ value
  value-nonnegative = limitsPres≤ (λ _ → 0ℝ) points 0ℝ value
    (constantIsLimitSequence 0ℝ) value-limit points-nonnegative

  value-square : value · value ≡ x
  value-square = limitSequenceUnique (λ n → points n · points n) (value · value) x
    (mulPresIsLimitSequence {x = points} {y = points} {l = value} {m = value}
      value-limit value-limit)
    (subst (λ sequence → isLimitSequence sequence x) (sym (funExt points-square))
      (subst (isLimitSequence shifted)
        (cong (x +_) (ℝRing.0RightAnnihilates 0ℝ) ∙ addIdR x)
        (addPresIsLimitSequence {x = λ _ → x} {y = λ n → radius n · radius n}
          {l = x} {m = 0ℝ · 0ℝ} (constantIsLimitSequence x)
          (mulPresIsLimitSequence {x = radius} {y = radius} {l = 0ℝ} {m = 0ℝ}
            radius-limit radius-limit))))

opaque
  nonnegativeSqrtℝ : (x : ℝ) → 0ℝ ≤ℝ x → ℝ
  nonnegativeSqrtℝ = Approximation.value

  nonnegativeSqrtℝ-nonnegative : ∀ x nonnegative → 0ℝ ≤ℝ nonnegativeSqrtℝ x nonnegative
  nonnegativeSqrtℝ-nonnegative = Approximation.value-nonnegative

  nonnegativeSqrtℝ-square : ∀ x nonnegative →
    nonnegativeSqrtℝ x nonnegative · nonnegativeSqrtℝ x nonnegative ≡ x
  nonnegativeSqrtℝ-square = Approximation.value-square

nonnegativeSqrtℝ-unique : ∀ x nonnegative y → 0ℝ ≤ℝ y → y · y ≡ x →
  y ≡ nonnegativeSqrtℝ x nonnegative
nonnegativeSqrtℝ-unique x nonnegative y yp square = squareInjectiveNonnegative
  y (nonnegativeSqrtℝ x nonnegative) yp (nonnegativeSqrtℝ-nonnegative x nonnegative)
  (square ∙ sym (nonnegativeSqrtℝ-square x nonnegative))
