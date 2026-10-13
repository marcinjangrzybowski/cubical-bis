module Cubical.Analysis.Real.Integration.RiemannIntegral.Extensionality where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
import Cubical.Data.FinData as FD
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Order
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Constant

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

opaque
  riemannSum-congOn : ∀ {a b} (tagged : TaggedPartition[ a , b ]) f g →
    (∀ x → a ≤ℝ x → x ≤ℝ b → f x ≡ g x) → riemannSum tagged f ≡ riemannSum tagged g
  riemannSum-congOn {a} {b} tagged f g agree = riemannSum-cong tagged f g
    (λ i → agree (TaggedPartition.tags tagged i)
      (≤ℝ-trans a (Partition.points p (FD.weakenFin i)) (TaggedPartition.tags tagged i)
        (partitionPointLowerBound p (FD.weakenFin i)) (TaggedPartition.lower≤tag tagged i))
      (≤ℝ-trans (TaggedPartition.tags tagged i) (Partition.points p (FD.suc i)) b
        (TaggedPartition.tag≤upper tagged i) (partitionPointUpperBound p (FD.suc i))))
    where
    p : Partition[ a , b ]
    p = TaggedPartition.partition tagged

  hasRiemannIntegral-congOn : ∀ f g a b value →
    (∀ x → a ≤ℝ x → x ≤ℝ b → f x ≡ g x) →
    HasRiemannIntegralOn f a b value → HasRiemannIntegralOn g a b value
  hasRiemannIntegral-congOn f g a b value agree hasValue ε =
    PT.map (λ { (δ , close) → δ , λ tagged fine →
      subst (λ s → absℝ (s - value) <ℝ rat (fst ε))
        (riemannSum-congOn tagged f g agree) (close tagged fine) }) (hasValue ε)

  riemannIntegrable-congOn : ∀ f g a b →
    (∀ x → a ≤ℝ x → x ≤ℝ b → f x ≡ g x) →
    IsRiemannIntegrableOn f a b → IsRiemannIntegrableOn g a b
  riemannIntegrable-congOn f g a b agree (value , hasValue) =
    value , hasRiemannIntegral-congOn f g a b value agree hasValue

  hasRiemannIntegralOnPoint : ∀ f a → HasRiemannIntegralOn f a a 0ℝ
  hasRiemannIntegralOnPoint f a =
    hasRiemannIntegral-congOn (λ _ → f a) f a a 0ℝ
      (λ x a≤x x≤a → cong f (≤ℝ-antisym a x a≤x x≤a))
      (subst (HasRiemannIntegralOn (λ _ → f a) a a)
        (cong (_· f a) (subSelf a) ∙ ℝRing.0LeftAnnihilates (f a))
        (constantHasRiemannIntegral a a (f a)))

  riemannIntegralOnPointIsZero : ∀ f a value → HasRiemannIntegralOn f a a value → value ≡ 0ℝ
  riemannIntegralOnPointIsZero f a value hasValue =
    riemannIntegralUnique a a (≤ℝ-refl a) f value 0ℝ hasValue (hasRiemannIntegralOnPoint f a)
