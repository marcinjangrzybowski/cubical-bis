module Cubical.Analysis.Complex.Contraction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Sequence
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Geometric
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Sequence.Geometric

private
  module R = RingTheory (CommRing→Ring ℝCommRing)

ComplexBall : ℂ → ℝ → ℂ → Type₀
ComplexBall center radius z = normℂ (z -ℂ center) ≤ℝ radius

-- A deterministic iteration supplies a single native sequence witness.
-- No selection of approximate fixed points, and no choice principle, occurs.
module Iteration (f : ℂ → ℂ) (center : ℂ) (radius q : ℝ)
  (radius-nonnegative : 0ℝ ≤ℝ radius)
  (q-nonnegative : 0ℝ ≤ℝ q) (q<one : q <ℝ 1ℝ)
  (preserves : ∀ z → ComplexBall center radius z → ComplexBall center radius (f z))
  (contracts : ∀ z w → ComplexBall center radius z → ComplexBall center radius w →
    normℂ (f z -ℂ f w) ≤ℝ q · normℂ (z -ℂ w)) where

  points : ℕ → ℂ
  points zero = center
  points (suc n) = f (points n)

  points-inBall : ∀ n → ComplexBall center radius (points n)
  points-inBall zero = subst (_≤ℝ radius)
    (sym (cong normℂ (+ℂInvR center) ∙ normℂ-zero)) radius-nonnegative
  points-inBall (suc n) = preserves (points n) (points-inBall n)

  increments : ℕ → ℝ
  increments n = normℂ (points (suc n) -ℂ points n)

  increments-contract : ∀ n → increments (suc n) ≤ℝ q · increments n
  increments-contract n = contracts (points (suc n)) (points n)
    (points-inBall (suc n)) (points-inBall n)

  opaque
    points-cauchy : ComplexSeqWitness points
    points-cauchy = geometricComplexIncrementsCauchy points q (increments zero)
      q-nonnegative q<one
      (contractionGeometricBound increments q q-nonnegative increments-contract)

    value : ℂ
    value = limitℂ points points-cauchy

    points-converge : IsComplexLimit points value
    points-converge = limitℂ-isLimit points points-cauchy

  opaque
    value-inBall : ComplexBall center radius value
    value-inBall = limitsPres≤
      (λ n → normℂ (points n -ℂ center)) (λ _ → radius)
      (normℂ (value -ℂ center)) radius
      (normℂ-preservesLimit (subComplexLimit points-converge (constantComplexLimit center)))
      (constantIsLimitSequence radius) points-inBall

    value-fixed : f value ≡ value
    value-fixed = sym (normℂ-difference-zero value (f value)
      (limitsPres≤
        (λ n → normℂ (points (suc n) -ℂ f value))
        (λ n → q · normℂ (points n -ℂ value))
        (normℂ (value -ℂ f value)) 0ℝ
        (normℂ-preservesLimit
          (subComplexLimit
            (shiftPresIsLimitSequence 1 _ _ (fst points-converge) ,
              shiftPresIsLimitSequence 1 _ _ (snd points-converge))
            (constantComplexLimit (f value))))
        (subst (isLimitSequence (λ n → q · normℂ (points n -ℂ value)))
          (cong (q ·_) (cong normℂ (+ℂInvR value) ∙ normℂ-zero)
            ∙ R.0RightAnnihilates q)
          (mulPresIsLimitSequence (constantIsLimitSequence q)
            (normℂ-preservesLimit (subComplexLimit points-converge (constantComplexLimit value)))))
        (λ n → contracts (points n) value (points-inBall n) value-inBall)))

    value-unique : ∀ z → ComplexBall center radius z → f z ≡ z → z ≡ value
    value-unique z z-inBall z-fixed = normℂ-difference-zero z value
      (subst (distance ≤ℝ_)
        (geometricallyBoundedNonnegativeLimitZero (λ _ → distance) distance q distance
          q-nonnegative q<one (constantIsLimitSequence distance)
          (λ _ → normℂ-nonnegative (z -ℂ value))
          (contractionGeometricBound (λ _ → distance) q q-nonnegative (λ _ → bound)))
        (≤ℝ-refl distance))
      where
      distance : ℝ
      distance = normℂ (z -ℂ value)

      bound : distance ≤ℝ q · distance
      bound = subst (λ d → d ≤ℝ q · distance)
        (cong normℂ (cong₂ _-ℂ_ z-fixed value-fixed))
        (contracts z value z-inBall value-inBall)

  fixedPoint : Σ[ z ∈ ℂ ] (ComplexBall center radius z × (f z ≡ z))
  fixedPoint = value , value-inBall , value-fixed
