module Cubical.Analysis.Real.Series.PowerSeries.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ
  using (ℕ; suc; _∸_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Product.Finite
open import Cubical.Analysis.Real.Series.PowerSeries.Base


private
  module ℝExponentiation = Exponentiation ℝCommRing

  powℝ-as-ringPower : ∀ x n →
    powℝ x n ≡ ℝExponentiation._^_ x n
  powℝ-as-ringPower x ℕ.zero = refl
  powℝ-as-ringPower x (suc n) =
    cong (x ·_) (powℝ-as-ringPower x n)


boundedPowerSplit : ∀ (x : ℝ) (n k : ℕ) →
  k ℕ.≤ n →
  powℝ x k · powℝ x (n ∸ k) ≡ powℝ x n
boundedPowerSplit x n k k≤n =
  cong₂ _·_
      (powℝ-as-ringPower x k)
      (powℝ-as-ringPower x (n ∸ k))
  ∙ ℝExponentiation.·-of-^-is-^-of-+ x k (n ∸ k)
  ∙ cong (ℝExponentiation._^_ x)
      ( ℕ.+-comm k (n ∸ k)
      ∙ ℕ.≤-∸-+-cancel k≤n)
  ∙ sym (powℝ-as-ringPower x n)


rearrangePowerSeriesTerm :
  ∀ (a b : RealSequence) (x : ℝ) (n k : ℕ) →
  k ℕ.≤ n →
  (a k · b (n ∸ k)) · powℝ x n
    ≡
  (a k · powℝ x k) ·
    (b (n ∸ k) · powℝ x (n ∸ k))
rearrangePowerSeriesTerm a b x n k k≤n =
  cong
    ((a k · b (n ∸ k)) ·_)
    (sym (boundedPowerSplit x n k k≤n))
  ∙ rearrange
      (a k) (b (n ∸ k))
      (powℝ x k) (powℝ x (n ∸ k))
  where
  rearrange : ∀ p q r s →
    (p · q) · (r · s) ≡ (p · r) · (q · s)
  rearrange p q r s =
    sym (mulAssoc p q (r · s))
    ∙ cong (p ·_) (mulAssoc q r s)
    ∙ cong (λ z → p · (z · s)) (mulComm q r)
    ∙ cong (p ·_) (sym (mulAssoc r q s))
    ∙ mulAssoc p r (q · s)


powerSeriesTerms-cauchyProduct :
  ∀ (a b : RealSequence) (x : ℝ) (n : ℕ) →
  powerSeriesTerms (cauchyProduct a b) x n
    ≡
  cauchyProduct
    (powerSeriesTerms a x) (powerSeriesTerms b x) n
powerSeriesTerms-cauchyProduct a b x n =
  sym
    (partialSum-right-scale
      (λ k → a k · b (n ∸ k))
      (powℝ x n) (suc n))
  ∙ partialSum-pointwiseBefore
      (λ k → (a k · b (n ∸ k)) · powℝ x n)
      (λ k →
        (a k · powℝ x k) ·
          (b (n ∸ k) · powℝ x (n ∸ k)))
      (suc n)
      (λ k k<sucn →
        rearrangePowerSeriesTerm
          a b x n k (ℕ.pred-≤-pred k<sucn))


powerSeriesTerms-cauchyProduct-sequence :
  ∀ (a b : RealSequence) (x : ℝ) →
  powerSeriesTerms (cauchyProduct a b) x
    ≡
  cauchyProduct (powerSeriesTerms a x) (powerSeriesTerms b x)
powerSeriesTerms-cauchyProduct-sequence a b x =
  funExt (powerSeriesTerms-cauchyProduct a b x)
