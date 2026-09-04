module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Density where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Base as ℚ using (ℚ)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Inverse as ℚInv using (1/2ⁿ<ε)
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Choice
  using (PositiveRationalChoice₀)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Choice


open PositiveRationals using (ℚ₊; [_/_]₊)
open 1/2∈ℚ

private
  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing

  dyadic : ℕ → ℚ₊
  dyadic n = [ 1 / 2 ]₊ ℚ₊^ⁿ n

  half<one : fst [ 1 / 2 ]₊ ℚ.< 1
  half<one =
    subst (fst [ 1 / 2 ]₊ ℚ.<_)
      (/2+/2≡id 1)
      (PositiveRationals.<₊SumLeft [ 1 / 2 ]₊ [ 1 / 2 ]₊)

  dyadicAntitone : ∀ m n → m ℕ.≤ n →
    fst (dyadic n) ℚ.≤ fst (dyadic m)
  dyadicAntitone m n m≤n =
    ℚOrder.powExponentAntitone (fst [ 1 / 2 ]₊)
      (ℚ.<Weaken≤ _ _ (snd [ 1 / 2 ]₊))
      (ℚ.<Weaken≤ _ _ half<one)
      m n m≤n

  dyadicEventuallyBelow : ∀ input →
    Σ[ N ∈ ℕ ]
      (∀ n → N ℕ.≤ n → fst (dyadic n) ℚ.< fst input)
  dyadicEventuallyBelow input =
    let N , at-N = 1/2ⁿ<ε input
    in N
     , λ n N≤n →
        ℚ.isTrans≤< _ _ _ (dyadicAntitone N n N≤n) at-N


SineQuarterApproximatePreimage : ℝ → ℝ → ℚ₊ → Type₀
SineQuarterApproximatePreimage quarter target tolerance =
  Σ[ point ∈ SineQuarterInterval quarter ]
    sinℝ (fst point) ∼[ tolerance ] target


SineQuarterApproximateImageDensity : ℝ → Type₀
SineQuarterApproximateImageDensity quarter =
  ∀ target → (- 1ℝ) ≤ℝ target → target ≤ℝ 1ℝ →
  ∀ tolerance →
    ∥ SineQuarterApproximatePreimage quarter target tolerance ∥₁


isPropSineQuarterApproximateImageDensity : ∀ quarter →
  isProp (SineQuarterApproximateImageDensity quarter)
isPropSineQuarterApproximateImageDensity quarter =
  isPropΠ4 λ _ _ _ _ → squash₁


chosenApproximatePreimages→imageApproximation :
  ∀ quarter target →
  (∀ tolerance →
    SineQuarterApproximatePreimage quarter target tolerance) →
  SineQuarterImageApproximation quarter target
chosenApproximatePreimages→imageApproximation
    quarter target approximate =
  (λ n → fst (approximate (dyadic n)))
  , λ input →
      let N , small = dyadicEventuallyBelow input
      in ∣ N
         , (λ n N≤n →
            S.isMonotone∼̂ₛ<
              (sinℝ (fst (fst (approximate (dyadic n)))))
              target (dyadic n) input (small n N≤n)
              (snd (approximate (dyadic n))))
         ∣₁


approximateImageDensity→imageApproximateIntermediateValue :
  ∀ quarter →
  PositiveRationalChoice₀ →
  SineQuarterApproximateImageDensity quarter →
  SineQuarterImageApproximateIntermediateValue quarter
approximateImageDensity→imageApproximateIntermediateValue
    quarter choice density target lower upper =
  PT.map
    (chosenApproximatePreimages→imageApproximation quarter target)
    (choice
      (SineQuarterApproximatePreimage quarter target)
      (density target lower upper))
