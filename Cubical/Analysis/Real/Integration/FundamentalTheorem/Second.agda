module Cubical.Analysis.Real.Integration.FundamentalTheorem.Second where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.FinData using (FinVec)
import Cubical.Data.FinData as FD
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.FiniteSum.Algebra
open import Cubical.Analysis.Real.FiniteSum.Bounds
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Order
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Algebra

private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)

open ℝSum using (∑)


-- Expand at the tag in both directions.  The two distances add to the
-- cell width, so no continuity hypothesis on the derivative is needed.
uniformDerivativeRiemannSumBound : ∀ F f a b (ε δ : ℚ₊) →
  (∀ x y →
    a ≤ℝ x → x ≤ℝ b → a ≤ℝ y → y ≤ℝ b →
    x ∼[ δ ] y →
    absℝ ((F y - F x) - f x · (y - x))
      ≤ℝ rat (fst ε) · absℝ (y - x)) →
  (tagged : TaggedPartition[ a , b ]) →
  HasMeshBelow (TaggedPartition.partition tagged) δ →
  absℝ (riemannSum tagged f - (F b - F a))
    ≤ℝ rat (fst ε) · (b - a)
uniformDerivativeRiemannSumBound F f a b ε δ remainder tagged mesh =
  subst2 _≤ℝ_
    (cong absℝ sumErrorPath
      ∙ absSubComm (F b - F a) (riemannSum tagged f))
    (sym (finiteSumMulLeft e (width p))
      ∙ cong (e ·_) (totalWidth p))
    (finiteSumAbsBoundBy errors (λ i → e · width p i) cellBound)
  where
  p = TaggedPartition.partition tagged
  open Partition p
  open TaggedPartition tagged using (tags; lower≤tag; tag≤upper)

  e = rat (fst ε)
  cellLeft = points ∘ FD.weakenFin
  cellRight = points ∘ FD.suc

  errors : FinVec ℝ intervalCount
  errors i = (F (cellRight i) - F (cellLeft i)) - width p i · f (tags i)

  a≤tag : ∀ i → a ≤ℝ tags i
  a≤tag i = ≤ℝ-trans a (cellLeft i) (tags i)
    (partitionPointLowerBound p (FD.weakenFin i)) (lower≤tag i)

  tag≤b : ∀ i → tags i ≤ℝ b
  tag≤b i = ≤ℝ-trans (tags i) (cellRight i) b (tag≤upper i)
    (partitionPointUpperBound p (FD.suc i))

  closeToTag : ∀ i y → cellLeft i ≤ℝ y → y ≤ℝ cellRight i →
    tags i ∼[ δ ] y
  closeToTag i y lower≤y y≤upper =
    absDifference<→closeness (tags i) y δ
      (≤<ℝ-trans (absℝ (tags i - y)) (width p i) (rat (fst δ))
        (pointsInIntervalDistanceBound (cellLeft i) (cellRight i) (tags i) y
          (lower≤tag i) (tag≤upper i) lower≤y y≤upper)
        (mesh i))

  errorAt : ∀ i → ℝ → ℝ
  errorAt i y = (F y - F (tags i)) - f (tags i) · (y - tags i)

  upperBound : ∀ i →
    absℝ (errorAt i (cellRight i)) ≤ℝ e · (cellRight i - tags i)
  upperBound i =
    subst (absℝ (errorAt i (cellRight i)) ≤ℝ_)
      (cong (e ·_)
        (absOfNonnegative (cellRight i - tags i)
          (nonnegativeSub (tags i) (cellRight i) (tag≤upper i))))
      (remainder (tags i) (cellRight i) (a≤tag i) (tag≤b i)
        (partitionPointLowerBound p (FD.suc i))
        (partitionPointUpperBound p (FD.suc i))
        (closeToTag i (cellRight i) (monotone i) (≤ℝ-refl (cellRight i))))

  lowerBound : ∀ i →
    absℝ (errorAt i (cellLeft i)) ≤ℝ e · (tags i - cellLeft i)
  lowerBound i =
    subst (absℝ (errorAt i (cellLeft i)) ≤ℝ_)
      (cong (e ·_)
        (absSubComm (cellLeft i) (tags i)
          ∙ absOfNonnegative (tags i - cellLeft i)
              (nonnegativeSub (cellLeft i) (tags i) (lower≤tag i))))
      (remainder (tags i) (cellLeft i) (a≤tag i) (tag≤b i)
        (partitionPointLowerBound p (FD.weakenFin i))
        (partitionPointUpperBound p (FD.weakenFin i))
        (closeToTag i (cellLeft i) (≤ℝ-refl (cellLeft i)) (monotone i)))

  cellBound : ∀ i → absℝ (errors i) ≤ℝ e · width p i
  cellBound i =
    subst2 _≤ℝ_
      (cong absℝ
        (remainderThrough (F (cellLeft i)) (F (cellRight i)) (F (tags i))
          (f (tags i)) (cellLeft i) (cellRight i) (tags i)
        ∙ cong ((F (cellRight i) - F (cellLeft i)) -_)
            (mulComm (f (tags i)) (width p i))))
      (sym (mulDistR e (cellRight i - tags i) (tags i - cellLeft i))
        ∙ cong (e ·_) (splitDifference (cellLeft i) (cellRight i) (tags i)))
      (≤ℝ-trans
        (absℝ (errorAt i (cellRight i) - errorAt i (cellLeft i)))
        (absℝ (errorAt i (cellRight i)) + absℝ (errorAt i (cellLeft i)))
        (e · (cellRight i - tags i) + e · (tags i - cellLeft i))
        (absSubTriangle (errorAt i (cellRight i)) (errorAt i (cellLeft i)))
        (addPres≤
          (absℝ (errorAt i (cellRight i))) (e · (cellRight i - tags i))
          (absℝ (errorAt i (cellLeft i))) (e · (tags i - cellLeft i))
          (upperBound i) (lowerBound i)))

  sumErrorPath : ∑ errors ≡ (F b - F a) - riemannSum tagged f
  sumErrorPath =
    finiteSumSub (λ i → F (cellRight i) - F (cellLeft i))
      (λ i → width p i · f (tags i))
    ∙ cong (_- riemannSum tagged f)
        (finiteSumTelescoping (F ∘ points)
          ∙ cong₂ _-_ (cong F rightEndpoint) (cong F leftEndpoint))


-- FTC, integration direction: a radiuswise uniform derivative is Riemann
-- integrable, with the endpoint difference as its value.  The integral is
-- constructed directly; a separate integrability assumption is unnecessary.
opaque
  fundamentalTheoremOfCalculusSecond : ∀ F f a b →
    IsRadiuswiseUniformDerivativeOn F f a b →
    HasRiemannIntegralOn f a b (F b - F a)
  fundamentalTheoremOfCalculusSecond F f a b derivative ε =
    PT.rec squash₁
      (λ { (n , length<n) →
        PT.map
          (λ { (δ , remainder) → δ , λ tagged mesh →
            ≤<ℝ-trans
              (absℝ (riemannSum tagged f - (F b - F a)))
              (rat (fst (ε ₊／₊ naturalBound n)) · (b - a))
              (rat (fst ε))
              (uniformDerivativeRiemannSumBound F f a b
                (ε ₊／₊ naturalBound n) δ remainder tagged mesh)
              (subst (_<ℝ_ (rat (fst (ε ₊／₊ naturalBound n)) · (b - a)))
                (mulComm (rat (fst (ε ₊／₊ naturalBound n)))
                    (rat (naturalRational n))
                  ∙ mul-rat (naturalRational n) (fst (ε ₊／₊ naturalBound n))
                  ∙ cong rat (·／ (naturalBound n) ε))
                (mulPres<PosL (b - a) (rat (naturalRational n))
                  (rat (fst (ε ₊／₊ naturalBound n)))
                  (<ℚ→<ℝ 0 (fst (ε ₊／₊ naturalBound n))
                    (snd (ε ₊／₊ naturalBound n)))
                  length<n)) })
          (derivative (ε ₊／₊ naturalBound n)) })
      (∃naturalUpperBound (b - a))

  uniformDerivativeIsRiemannIntegrable : ∀ F f a b →
    IsRadiuswiseUniformDerivativeOn F f a b →
    IsRiemannIntegrableOn f a b
  uniformDerivativeIsRiemannIntegrable F f a b derivative =
    (F b - F a) , fundamentalTheoremOfCalculusSecond F f a b derivative

  integralOfUniformDerivative : ∀ F f a b → a ≤ℝ b →
    IsRadiuswiseUniformDerivativeOn F f a b →
    (integrable : IsRiemannIntegrableOn f a b) →
    integral {f = f} {a = a} {b = b} integrable ≡ F b - F a
  integralOfUniformDerivative F f a b a≤b derivative integrable =
    riemannIntegralUnique a b a≤b f (fst integrable) (F b - F a)
      (snd integrable) (fundamentalTheoremOfCalculusSecond F f a b derivative)
