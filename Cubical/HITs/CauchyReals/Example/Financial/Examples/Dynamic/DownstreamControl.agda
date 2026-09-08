{-# OPTIONS --safe --cubical #-}

-- Nested coherent risk is motivated by ../../REFERENCES.md#shapiro-2016.
-- This synthetic tree composes worst-case branch risk with conditional
-- expectation. Its consistency theorem concerns that specified recursion;
-- it does not identify the result with a static CVaR evaluation.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.Dynamic.DownstreamControl where

open import Cubical.HITs.CauchyReals.Example.Financial.Dynamic.Base
open import Cubical.HITs.CauchyReals.Example.Financial.Core.Probability public
import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase as W
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.FinData.Base as F
import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Example.Financial.Examples.CommonScenarioData public
  using (two; half; fair)

-- The first uncertainty is treated robustly; after it is observed, the
-- two conditional leaves are equiprobable. This is a nested risk model.
module Evaluation = TwoStage (worstCaseRisk {1}) (λ _ → expectationRisk fair)

before after : LossTree 2 2
before F.zero = two 8 -2
before (F.suc F.zero) = two 0 2
after F.zero = two 2 0
after (F.suc F.zero) = two 0 2

before-conditional : Evaluation.continuationRisk before ≡ two 3 1
before-conditional = funExt λ
  { F.zero → ℝ!
  ; (F.suc F.zero) → ℝ!
  }

after-conditional : Evaluation.continuationRisk after ≡ two 1 1
after-conditional = funExt λ
  { F.zero → ℝ!
  ; (F.suc F.zero) → ℝ!
  }

conditional-improvement : ∀ i →
  Evaluation.continuationRisk after i ≤ᵣ Evaluation.continuationRisk before i
conditional-improvement i = subst2 _≤ᵣ_
  (sym (funExt⁻ after-conditional i)) (sym (funExt⁻ before-conditional i))
  (numerical i)
  where
  numerical : ∀ i → two 1 1 i ≤ᵣ two 3 1 i
  numerical F.zero = decℚ≤ᵣ?
  numerical (F.suc F.zero) = decℚ≤ᵣ?

initial-improvement : Evaluation.rootRisk after ≤ᵣ Evaluation.rootRisk before
initial-improvement = Evaluation.strong-time-consistency after before conditional-improvement

private
  maximum-two : ∀ a b → b ≤ᵣ a → W.worstCase (two a b) ≡ a
  maximum-two a b bound = isAntisym≤ᵣ _ _
    (W.worstCase-least (two a b) a upper)
    (W.worstCase-upper (two a b) F.zero)
    where
    upper : ∀ i → two a b i ≤ᵣ a
    upper F.zero = ≤ᵣ-refl a
    upper (F.suc F.zero) = bound

before-capital : Evaluation.rootRisk before ≡ 3
before-capital = cong W.worstCase before-conditional ∙ maximum-two 3 1 decℚ≤ᵣ?

after-capital : Evaluation.rootRisk after ≡ 1
after-capital = cong W.worstCase after-conditional ∙ maximum-two 1 1 decℚ≤ᵣ?

strict-capital-improvement : Evaluation.rootRisk after <ᵣ Evaluation.rootRisk before
strict-capital-improvement =
  subst2 _<ᵣ_ (sym after-capital) (sym before-capital) decℚ<ᵣ?

capital-one-certificate : Evaluation.NodeBudgetCertificate after 1
capital-one-certificate = Evaluation.node-certificate-complete after 1
  (≡ᵣWeaken≤ᵣ _ _ after-capital)

-- Giving up a gain in one leaf is allowed: the revised first branch has
-- lower conditional risk even though leafwise dominance does not hold.
gain-given-up : before F.zero (F.suc F.zero) <ᵣ after F.zero (F.suc F.zero)
gain-given-up = decℚ<ᵣ?
