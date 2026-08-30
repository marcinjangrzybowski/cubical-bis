module Cubical.Analysis.Real.Series.PowerSeries.Product.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ
  using (ℕ; zero; suc; _∸_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.FiniteSum.Reindexing
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.Product.Finite
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)

  weightedProductSplit : ∀ (a b : RealSequence) n k →
    k ℕ.≤ suc n →
    realNatural (suc n) · (a k · b (suc n ∸ k))
      ≡
    (realNatural k · a k) · b (suc n ∸ k)
      + a k ·
          (realNatural (suc n ∸ k) · b (suc n ∸ k))
  weightedProductSplit a b n k k≤sucn =
    cong (_· (a k · b (suc n ∸ k)))
      ( cong realNatural
          (sym
            (ℕ.+-comm k (suc n ∸ k)
            ∙ ℕ.[n-m]+m k (suc n) k≤sucn))
      ∙ realNatural-add k (suc n ∸ k)
      )
    ∙ mulDistL
        (realNatural k)
        (realNatural (suc n ∸ k))
        (a k · b (suc n ∸ k))
    ∙ cong₂ _+_
        (mulAssoc
          (realNatural k) (a k) (b (suc n ∸ k)))
        ( mulAssoc
            (realNatural (suc n ∸ k))
            (a k) (b (suc n ∸ k))
        ∙ cong (_· b (suc n ∸ k))
            (mulComm (realNatural (suc n ∸ k)) (a k))
        ∙ sym
            (mulAssoc
              (a k)
              (realNatural (suc n ∸ k))
              (b (suc n ∸ k)))
        )

  leftWeightedSum : ∀ (a b : RealSequence) n →
    partialSum
        (λ k →
          (realNatural k · a k) · b (suc n ∸ k))
        (suc (suc n))
      ≡
    cauchyProduct (formalDerivative a) b n
  leftWeightedSum a b n =
    partialSum-first
      (λ k →
        (realNatural k · a k) · b (suc n ∸ k))
      (suc n)
    ∙ cong
        (_+ partialSum
          (λ k →
            (realNatural (suc k) · a (suc k))
              · b (n ∸ k))
          (suc n))
        ( cong (_· b (suc n))
            (ℝRing.0LeftAnnihilates (a zero))
        ∙ ℝRing.0LeftAnnihilates (b (suc n))
        )
    ∙ addIdL
        (partialSum
          (λ k →
            (realNatural (suc k) · a (suc k))
              · b (n ∸ k))
          (suc n))

  rightWeightedSum : ∀ (a b : RealSequence) n →
    partialSum
        (λ k →
          a k ·
            (realNatural (suc n ∸ k) · b (suc n ∸ k)))
        (suc (suc n))
      ≡
    cauchyProduct a (formalDerivative b) n
  rightWeightedSum a b n =
    cong₂ _+_
      (partialSum-pointwiseBefore
        (λ k →
          a k ·
            (realNatural (suc n ∸ k) · b (suc n ∸ k)))
        (λ k →
          a k ·
            (realNatural (suc (n ∸ k)) · b (suc (n ∸ k))))
        (suc n)
        (λ k k<sucn →
          cong
            (λ index →
              a k · (realNatural index · b index))
            (sym
              (ℕ.≤-∸-suc
                (ℕ.pred-≤-pred k<sucn)))))
      ( cong
          (λ index →
            a (suc n) · (realNatural index · b index))
          (ℕ.n∸n≡0 (suc n))
      ∙ cong (a (suc n) ·_)
          (ℝRing.0LeftAnnihilates (b zero))
      ∙ ℝRing.0RightAnnihilates (a (suc n))
      )
    ∙ addIdR
        (partialSum
          (λ k →
            a k ·
              (realNatural (suc (n ∸ k)) · b (suc (n ∸ k))))
          (suc n))


-- Formal Leibniz rule on the nth finite anti-diagonal.  This is purely a
-- coefficient identity; no summability assumption is involved.
formalDerivative-cauchyProduct-pointwise : ∀ a b n →
  formalDerivative (cauchyProduct a b) n
    ≡
  cauchyProduct (formalDerivative a) b n
    + cauchyProduct a (formalDerivative b) n
formalDerivative-cauchyProduct-pointwise a b n =
  sym
    (partialSum-scale
      (realNatural (suc n))
      (λ k → a k · b (suc n ∸ k))
      (suc (suc n)))
  ∙ partialSum-pointwiseBefore
      (λ k →
        realNatural (suc n) · (a k · b (suc n ∸ k)))
      (λ k →
        (realNatural k · a k) · b (suc n ∸ k)
          + a k ·
              (realNatural (suc n ∸ k) · b (suc n ∸ k)))
      (suc (suc n))
      (λ k k<sucsucn →
        weightedProductSplit a b n k
          (ℕ.pred-≤-pred k<sucsucn))
  ∙ partialSum-add
      (λ k →
        (realNatural k · a k) · b (suc n ∸ k))
      (λ k →
        a k ·
          (realNatural (suc n ∸ k) · b (suc n ∸ k)))
      (suc (suc n))
  ∙ cong₂ _+_
      (leftWeightedSum a b n)
      (rightWeightedSum a b n)


formalDerivative-cauchyProduct : ∀ a b →
  formalDerivative (cauchyProduct a b)
    ≡
  (λ n →
    cauchyProduct (formalDerivative a) b n
      + cauchyProduct a (formalDerivative b) n)
formalDerivative-cauchyProduct a b =
  funExt (formalDerivative-cauchyProduct-pointwise a b)
