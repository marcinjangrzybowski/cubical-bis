module Cubical.Analysis.Real.Integration.RiemannIntegral.Ordered.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (1₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties using (≤ℝ→≯)
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Order
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Constant
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Add
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Neg
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Sub
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Scale
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Ordered


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


module _ (interval : OrderedIntegrationInterval) where
  private
    a = integrationLowerEndpoint interval
    b = integrationUpperEndpoint interval

  constantHasRiemannIntegralOnInterval : ∀ c →
    HasRiemannIntegralOnInterval (λ _ → c) interval ((b - a) · c)
  constantHasRiemannIntegralOnInterval = constantHasRiemannIntegral a b

  constantIsRiemannIntegrableOnInterval : ∀ c →
    IsRiemannIntegrableOnInterval (λ _ → c) interval
  constantIsRiemannIntegrableOnInterval = constantIsRiemannIntegrable a b

  integralOnInterval-constant : ∀ c →
    integralOnInterval interval {λ _ → c}
      (constantIsRiemannIntegrableOnInterval c) ≡ (b - a) · c
  integralOnInterval-constant c = refl

  addHasRiemannIntegralOnInterval : ∀ f g value value' →
    HasRiemannIntegralOnInterval f interval value →
    HasRiemannIntegralOnInterval g interval value' →
    HasRiemannIntegralOnInterval (λ x → f x + g x) interval (value + value')
  addHasRiemannIntegralOnInterval = addHasRiemannIntegral {a} {b}

  addIsRiemannIntegrableOnInterval : ∀ f g →
    IsRiemannIntegrableOnInterval f interval →
    IsRiemannIntegrableOnInterval g interval →
    IsRiemannIntegrableOnInterval (λ x → f x + g x) interval
  addIsRiemannIntegrableOnInterval = addIsRiemannIntegrable {a} {b}

  negHasRiemannIntegralOnInterval : ∀ f value →
    HasRiemannIntegralOnInterval f interval value →
    HasRiemannIntegralOnInterval (λ x → - f x) interval (- value)
  negHasRiemannIntegralOnInterval = negHasRiemannIntegral {a} {b}

  negIsRiemannIntegrableOnInterval : ∀ f →
    IsRiemannIntegrableOnInterval f interval →
    IsRiemannIntegrableOnInterval (λ x → - f x) interval
  negIsRiemannIntegrableOnInterval = negIsRiemannIntegrable {a} {b}

  subHasRiemannIntegralOnInterval : ∀ f g value value' →
    HasRiemannIntegralOnInterval f interval value →
    HasRiemannIntegralOnInterval g interval value' →
    HasRiemannIntegralOnInterval (λ x → f x - g x) interval (value - value')
  subHasRiemannIntegralOnInterval = subHasRiemannIntegral {a} {b}

  subIsRiemannIntegrableOnInterval : ∀ f g →
    IsRiemannIntegrableOnInterval f interval →
    IsRiemannIntegrableOnInterval g interval →
    IsRiemannIntegrableOnInterval (λ x → f x - g x) interval
  subIsRiemannIntegrableOnInterval = subIsRiemannIntegrable {a} {b}

  scaleHasRiemannIntegralOnInterval : ∀ c f value →
    HasRiemannIntegralOnInterval f interval value →
    HasRiemannIntegralOnInterval (λ x → c · f x) interval (c · value)
  scaleHasRiemannIntegralOnInterval = scaleHasRiemannIntegral {a} {b}

  scaleIsRiemannIntegrableOnInterval : ∀ c f →
    IsRiemannIntegrableOnInterval f interval →
    IsRiemannIntegrableOnInterval (λ x → c · f x) interval
  scaleIsRiemannIntegrableOnInterval = scaleIsRiemannIntegrable {a} {b}


opaque
  -- Degenerate ordered intervals remain valid, with the expected value.
  constantHasRiemannIntegralOnPoint : ∀ a c →
    HasRiemannIntegralOnInterval (λ _ → c) (pointIntegrationInterval a) 0ℝ
  constantHasRiemannIntegralOnPoint a c =
    subst (HasRiemannIntegralOnInterval (λ _ → c) (pointIntegrationInterval a))
      (cong (_· c) (subSelf a) ∙ ℝRing.0LeftAnnihilates c)
      (constantHasRiemannIntegralOnInterval (pointIntegrationInterval a) c)

  constantIntegralOnPointIsZero : ∀ a c
    (integrable :
      IsRiemannIntegrableOnInterval (λ _ → c) (pointIntegrationInterval a)) →
    integralOnInterval (pointIntegrationInterval a) {λ _ → c} integrable ≡ 0ℝ
  constantIntegralOnPointIsZero a c integrable =
    riemannIntegralOnIntervalUnique
      (pointIntegrationInterval a) (λ _ → c) (fst integrable) 0ℝ
      (snd integrable) (constantHasRiemannIntegralOnPoint a c)

  reversedEndpointsHaveNoPartition : ∀ a b →
    b <ℝ a → ¬ Partition[ a , b ]
  reversedEndpointsHaveNoPartition a b b<a partition =
    ≤ℝ→≯ a b (partitionEndpointsOrdered partition) b<a

  -- Regression documenting why the ordered wrapper is needed: the old
  -- predicate accepts every candidate value when its partition domain is empty.
  reversedIntervalIntegralIsVacuous : ∀ a b → b <ℝ a → ∀ f value →
    HasRiemannIntegralOn f a b value
  reversedIntervalIntegralIsVacuous a b b<a f value ε =
    ∣ (1₊ , λ tagged _ →
      ⊥.rec (reversedEndpointsHaveNoPartition a b b<a
        (TaggedPartition.partition tagged))) ∣₁
