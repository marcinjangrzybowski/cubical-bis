{-# OPTIONS --safe --cubical #-}

-- Shared synthetic probabilities and capped dual scenario weights.
-- See ../REFERENCES.md#synthetic-parameters, #rockafellar-uryasev-2002
-- and #shapiro-2016. Equal scenario weights and multiplier 2 (50% tail)
-- are illustrative inputs, not calibrated market or default probabilities.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.CommonScenarioData where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Vectors public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.ExpectedShortfall
open import Cubical.HITs.CauchyReals.Foundation.Rationals using ([_/_])
open import Cubical.Data.NatPlusOne using (fromNatℕ₊₁)
open import Cubical.Data.Int.Base using (fromNatℤ)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.FinData.Base as F

-- Reusable illustrative scenario data, independent of any asset or broker.
-- These probabilities are supplied example inputs, not an empirical
-- calibration or probabilities of client default.
half quarter : ℝ
half = rat [ 1 / 2 ]
quarter = rat [ 1 / 4 ]

equalProbability : Distribution 4
equalProbability = (λ _ → quarter) , (λ _ → decℚ≤ᵣ?) , total
  where
  total : sum {4} (λ _ → quarter) ≡ 1
  total = ℝ!

halfTail : TailLevel
halfTail = tail-level 2 decℚ≤ᵣ?

fair : Distribution 2
fair = (λ _ → half) , (λ _ → decℚ≤ᵣ?) , total
  where
  total : sum {2} (λ _ → half) ≡ 1
  total = ℝ!

-- The stress names identify their two nonzero scenario coordinates.
-- Their density caps depend only on the uniform base measure and tail
-- level; optimality for a particular loss profile is proved by each example.
private
  module HalfTail = TailRisk equalProbability halfTail
open HalfTail using (Admissible)

-- Each dual measure has unit mass and respects q_i ≤ 2 p_i.
stress02 stress12 stress01 : Distribution 4
stress02 = four half 0 half 0 , nonnegative , total
  where
  nonnegative : ∀ i → 0 ≤ᵣ four half 0 half 0 i
  nonnegative F.zero = decℚ≤ᵣ?
  nonnegative (F.suc F.zero) = decℚ≤ᵣ?
  nonnegative (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  nonnegative (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?
  total : sum (four half 0 half 0) ≡ 1
  total = ℝ!
stress12 = four 0 half half 0 , nonnegative , total
  where
  nonnegative : ∀ i → 0 ≤ᵣ four 0 half half 0 i
  nonnegative F.zero = decℚ≤ᵣ?
  nonnegative (F.suc F.zero) = decℚ≤ᵣ?
  nonnegative (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  nonnegative (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?
  total : sum (four 0 half half 0) ≡ 1
  total = ℝ!
stress01 = four half half 0 0 , nonnegative , total
  where
  nonnegative : ∀ i → 0 ≤ᵣ four half half 0 0 i
  nonnegative F.zero = decℚ≤ᵣ?
  nonnegative (F.suc F.zero) = decℚ≤ᵣ?
  nonnegative (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  nonnegative (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?
  total : sum (four half half 0 0) ≡ 1
  total = ℝ!

private
  half-cap : half ≤ᵣ 2 ·ᵣ quarter
  half-cap = ≡ᵣWeaken≤ᵣ _ _ ℝ!

  zero-cap : 0 ≤ᵣ 2 ·ᵣ quarter
  zero-cap = isTrans≤ᵣ _ _ _ decℚ≤ᵣ? half-cap

stress02-admissible : Admissible stress02
stress02-admissible F.zero = half-cap
stress02-admissible (F.suc F.zero) = zero-cap
stress02-admissible (F.suc (F.suc F.zero)) = half-cap
stress02-admissible (F.suc (F.suc (F.suc F.zero))) = zero-cap

stress12-admissible : Admissible stress12
stress12-admissible F.zero = zero-cap
stress12-admissible (F.suc F.zero) = half-cap
stress12-admissible (F.suc (F.suc F.zero)) = half-cap
stress12-admissible (F.suc (F.suc (F.suc F.zero))) = zero-cap

stress01-admissible : Admissible stress01
stress01-admissible F.zero = half-cap
stress01-admissible (F.suc F.zero) = half-cap
stress01-admissible (F.suc (F.suc F.zero)) = zero-cap
stress01-admissible (F.suc (F.suc (F.suc F.zero))) = zero-cap
