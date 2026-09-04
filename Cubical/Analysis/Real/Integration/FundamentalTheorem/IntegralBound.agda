module Cubical.Analysis.Real.Integration.FundamentalTheorem.IntegralBound where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.FinData using (FinVec)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_; isProp<ℝ)
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.FiniteSum.Algebra
open import Cubical.Analysis.Real.FiniteSum.Bounds
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base


private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)

open ℝSum using (∑)


-- A pointwise absolute bound passes to every tagged Riemann sum.  The
-- nonnegative cell widths are the only sign information needed here.

riemannSum-absBound : ∀ {a b}
  (tagged : TaggedPartition[ a , b ])
  (f : ℝ → ℝ) (bound : ℝ) →
  (∀ x → absℝ (f x) ≤ℝ bound) →
  absℝ (riemannSum tagged f) ≤ℝ (b - a) · bound
riemannSum-absBound {a} {b} tagged f bound pointwise =
  subst2 _≤ℝ_ refl totalBoundPath
    (≤ℝ-trans
      (absℝ (∑ terms))
      (∑ (absℝ ∘ terms))
      (∑ boundTerms)
      (finiteSumAbsBound terms)
      (finiteSumMono (absℝ ∘ terms) boundTerms termBound))
  where
  partition = TaggedPartition.partition tagged
  tags = TaggedPartition.tags tagged

  terms : FinVec ℝ (Partition.intervalCount partition)
  terms i = width partition i · f (tags i)

  boundTerms : FinVec ℝ (Partition.intervalCount partition)
  boundTerms i = width partition i · bound

  termBound : ∀ i → absℝ (terms i) ≤ℝ boundTerms i
  termBound i =
    subst (_≤ℝ boundTerms i)
      (sym
        (absMul (width partition i) (f (tags i))
        ∙ cong (_· absℝ (f (tags i)))
            (absOfNonnegative
              (width partition i) (width-nonnegative partition i))))
      (mulPres≤L
        (absℝ (f (tags i))) bound (width partition i)
        (0≤→isNonnegative
          (width partition i) (width-nonnegative partition i))
        (pointwise (tags i)))

  totalBoundPath : ∑ boundTerms ≡ (b - a) · bound
  totalBoundPath =
    sym (finiteSumMulRight bound (width partition))
    ∙ cong (_· bound) (totalWidth partition)


-- This is the semantic Riemann-integral analogue of the usual
-- |integral f| ≤ (b-a)B estimate.  Approximate the integral by one fine
-- tagged sum, use the preceding finite bound, and then close the order by
-- arbitrarily small rational slack.

riemannIntegral-absBound : ∀ a b → a ≤ℝ b →
  ∀ f value bound →
  HasRiemannIntegralOn f a b value →
  (∀ x → absℝ (f x) ≤ℝ bound) →
  absℝ value ≤ℝ (b - a) · bound
riemannIntegral-absBound a b a≤b f value bound hasIntegral pointwise =
  arbitrarilySmallSlack→≤
    (absℝ value) ((b - a) · bound)
    (λ ε →
      PT.rec
        (isProp<ℝ
          (absℝ value)
          ((b - a) · bound + rat (fst ε)))
        (λ { (δ , closeToValue) →
          PT.rec
            (isProp<ℝ
              (absℝ value)
              ((b - a) · bound + rat (fst ε)))
            (λ { (tagged , fine) →
              estimate ε tagged (closeToValue tagged fine) })
            (fineTaggedPartition a b a≤b δ) })
        (hasIntegral ε))
  where
  estimate : ∀ (ε : ℚ₊) tagged →
    absℝ (riemannSum tagged f - value) <ℝ rat (fst ε) →
    absℝ value <ℝ (b - a) · bound + rat (fst ε)
  estimate ε tagged close =
    subst2 _<ℝ_ valueBoundPath (addComm _ _)
      (<≤ℝ-add
        (absℝ (value - riemannSum tagged f))
        (rat (fst ε))
        (absℝ (riemannSum tagged f))
        ((b - a) · bound)
        (subst (_<ℝ rat (fst ε))
          (absSubComm value (riemannSum tagged f)) close)
        (riemannSum-absBound tagged f bound pointwise))
    where
    valueAsDifferencePlusSum :
      (value - riemannSum tagged f) + riemannSum tagged f ≡ value
    valueAsDifferencePlusSum =
      addAssoc value ((-_) (riemannSum tagged f)) (riemannSum tagged f)
      ∙ cong (value +_) (addInvL (riemannSum tagged f))
      ∙ addIdR value

    valueBoundPath :
      absℝ value ≡
      absℝ ((value - riemannSum tagged f) + riemannSum tagged f)
    valueBoundPath = cong absℝ (sym valueAsDifferencePlusSum)
