-- Covariance-based portfolio diversification follows the method discussed in
-- ../../REFERENCES.md#markowitz-1952. The loss vectors are synthetic:
-- the completed-square identity proves the minimum for this example,
-- without claiming that variance alone measures every relevant risk.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.VarianceExample where

open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Variance
import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Diversification as D
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- The same four-scenario portfolio has a dispersion interpretation. Each
-- asset has mean loss 1 and variance 9. Their covariance is negative, so
-- combining them reduces both tail risk and variance in this example.
variance-A : variance D.equalProbability D.assetA ≡ 9
variance-A = ℝ!

variance-B : variance D.equalProbability D.assetB ≡ 9
variance-B = ℝ!

covariance-AB : covariance D.equalProbability D.assetA D.assetB ≡ -7
covariance-AB = ℝ!

-- Complete the square after using the general two-asset theorem. The
-- identity holds over all Cauchy-real weights, including leverage/shorting.
variance-mixed : ∀ w → variance D.equalProbability (D.mixed w)
  ≡ 1 +ᵣ 32 ·ᵣ square (w -ᵣ D.half)
variance-mixed w =
  variance-two-assets D.equalProbability w (1 -ᵣ w) D.assetA D.assetB
  ∙ cong₃ (λ a c b →
      (square w ·ᵣ a +ᵣ 2 ·ᵣ (w ·ᵣ ((1 -ᵣ w) ·ᵣ c)))
        +ᵣ square (1 -ᵣ w) ·ᵣ b)
      variance-A covariance-AB variance-B
  ∙ ℝ!

variance-balanced : variance D.equalProbability D.balanced ≡ 1
variance-balanced = variance-mixed D.half ∙ ℝ!

all-portfolios-variance-lower-bound : ∀ w →
  1 ≤ᵣ variance D.equalProbability (D.mixed w)
all-portfolios-variance-lower-bound w =
  isTrans≤≡ᵣ _ _ _
    (isTrans≡≤ᵣ _ _ _ (sym (+IdR 1))
      (≤ᵣ-o+ 0 (32 ·ᵣ square (w -ᵣ D.half)) 1
        (nonnegative-mul 32 (square (w -ᵣ D.half)) decℚ≤ᵣ?
          (square-nonnegative (w -ᵣ D.half)))))
    (sym (variance-mixed w))

balanced-global-variance-optimum : ∀ w →
  variance D.equalProbability D.balanced
    ≤ᵣ variance D.equalProbability (D.mixed w)
balanced-global-variance-optimum w =
  isTrans≡≤ᵣ _ _ _ variance-balanced (all-portfolios-variance-lower-bound w)

variance-strict-improvement-A :
  variance D.equalProbability D.balanced <ᵣ variance D.equalProbability D.assetA
variance-strict-improvement-A =
  subst2 _<ᵣ_ (sym variance-balanced) (sym variance-A) decℚ<ᵣ?

variance-strict-improvement-B :
  variance D.equalProbability D.balanced <ᵣ variance D.equalProbability D.assetB
variance-strict-improvement-B =
  subst2 _<ᵣ_ (sym variance-balanced) (sym variance-B) decℚ<ᵣ?

-- The quarter-weight allocation shares the optimal CVaR value 2, but its
-- variance is 3. Dispersion therefore distinguishes these tail-risk ties.
variance-quarter : variance D.equalProbability (D.mixed D.quarter) ≡ 3
variance-quarter = variance-mixed D.quarter ∙ ℝ!

balanced-less-variable-than-quarter :
  variance D.equalProbability D.balanced
    <ᵣ variance D.equalProbability (D.mixed D.quarter)
balanced-less-variable-than-quarter =
  subst2 _<ᵣ_ (sym variance-balanced) (sym variance-quarter) decℚ<ᵣ?
