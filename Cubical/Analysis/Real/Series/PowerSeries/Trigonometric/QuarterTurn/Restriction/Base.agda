module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

open import Cubical.Algebra.OrderedCommRing

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (negInvol; negZero)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue using (absℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition using (negPres≤)
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Structure
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Domain.Interval
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.SharpBounds


SineQuarterInterval : ℝ → Type₀
SineQuarterInterval quarter =
  ClosedInterval (- quarter) quarter


SineUnitInterval : Type₀
SineUnitInterval =
  ClosedInterval (- 1ℝ) 1ℝ


private
  zero≤one : 0ℝ ≤ℝ 1ℝ
  zero≤one =
    <ℝ-weaken 0ℝ 1ℝ
      (isOrderedCommRingℝ .IsOrderedCommRing.0<1)

sineUnitEndpointsOrdered : (- 1ℝ) ≤ℝ 1ℝ
sineUnitEndpointsOrdered =
  ≤ℝ-trans (- 1ℝ) 0ℝ 1ℝ
    (subst ((- 1ℝ) ≤ℝ_) negZero
      (negPres≤ 0ℝ 1ℝ zero≤one))
    zero≤one


sineUnitLeft : SineUnitInterval
sineUnitLeft =
  (- 1ℝ) , ≤ℝ-refl (- 1ℝ) , sineUnitEndpointsOrdered


sineUnitRight : SineUnitInterval
sineUnitRight =
  1ℝ , sineUnitEndpointsOrdered , ≤ℝ-refl 1ℝ


opaque
  sineUnitInterval≡ : (left right : SineUnitInterval) →
    fst left ≡ fst right → left ≡ right
  sineUnitInterval≡ left right =
    Σ≡Prop
      (isPropClosedIntervalMembership (- 1ℝ) 1ℝ)


opaque
  restrictedSine : ∀ quarter →
    SineQuarterInterval quarter → SineUnitInterval
  restrictedSine quarter point =
    symmetricIntervalFromAbsBound 1ℝ (sinℝ (fst point))
      (sinℝ-abs≤one (fst point))


  restrictedSine-value : ∀ quarter point →
    fst (restrictedSine quarter point) ≡ sinℝ (fst point)
  restrictedSine-value quarter point = refl
