{-# OPTIONS --safe --cubical #-}

-- Separate close-out netting sets follow the risk distinction in
-- ../../REFERENCES.md#bcbs-settlement-2013. The opposite claims +/-10
-- are synthetic. Their aggregate cancellation grants no cross-client
-- netting right; the failure of quotient invariance is proved here.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.Netting.OppositeClaims where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Vectors public using (two)

open import Cubical.HITs.CauchyReals.Example.Financial.Margin.ClientNetting
open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Example.Financial.Core.EconomicEquivalence
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.FinData.Base as F

opposite emptyBook : Vector 2
opposite = two 10 -10
emptyBook = λ _ → 0

opposite-mark-zero : sum opposite ≡ 0
opposite-mark-zero = ℝ!

opposite-exposure-ten : separateExposure opposite ≡ 10
opposite-exposure-ten = sum-cong (λ i → positivePart (opposite i)) (two 10 0) values ∙ ℝ!
  where
  values : ∀ i → positivePart (opposite i) ≡ two 10 0 i
  values F.zero = positivePart-of-nonnegative 10 decℚ≤ᵣ?
  values (F.suc F.zero) = positivePart-of-nonpositive -10 decℚ≤ᵣ?

empty-exposure-zero : separateExposure emptyBook ≡ 0
empty-exposure-zero = sum-cong (λ i → positivePart (emptyBook i)) emptyBook
  (λ i → positivePart-zero) ∙ sum-zero 2

opposite-residual-ten : brokerResidual opposite emptyBook ≡ 10
opposite-residual-ten = brokerResidual-no-collateral opposite ∙ opposite-exposure-ten

opposite-pooled-zero : pooledResidual opposite emptyBook ≡ 0
opposite-pooled-zero = cong₂ stopLoss opposite-mark-zero (sum-zero 2)
  ∙ stopLoss-zero-below 0 0 (≤ᵣ-refl 0)

-- Total marks erase client identity. This quotient identifies the
-- opposite claims with an empty book, although exposure differs by 10.
module Aggregate = EconomicModel (Fin 1) (Vector 2) (λ claims _ → sum claims)

same-aggregate-class : Aggregate.class opposite ≡ Aggregate.class emptyBook
same-aggregate-class = Aggregate.class-sound
  (λ _ → opposite-mark-zero ∙ sym (sum-zero 2))

no-separate-exposure-descent : (f : Aggregate.EconomicClass → ℝ) →
  (∀ claims → f (Aggregate.class claims) ≡ separateExposure claims) → ⊥
no-separate-exposure-descent f agrees = isIrrefl<ᵣ 0
  (isTrans<≡ᵣ 0 10 0 decℚ<ᵣ? ten-is-zero)
  where
  ten-is-zero : _≡_ {A = ℝ} 10 0
  ten-is-zero = sym opposite-exposure-ten ∙ sym (agrees opposite)
    ∙ cong f same-aggregate-class ∙ agrees emptyBook ∙ empty-exposure-zero
