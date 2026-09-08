{-# OPTIONS --safe --cubical #-}

-- Rectangular ambiguity and dynamic consistency are discussed in
-- ../../REFERENCES.md#epstein-schneider-2003 and #shapiro-2016.
-- The synthetic tree separates coupled models from branch-dependent choices;
-- the exact risk gap 2 versus 4 is an example, not a general gap formula.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.Dynamic.RectangularGap where

open import Cubical.HITs.CauchyReals.Example.Financial.Dynamic.Ambiguity
open import Cubical.HITs.CauchyReals.Example.Financial.Dynamic.Base public
import Cubical.HITs.CauchyReals.Example.Financial.Risk.Ambiguity as A
import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase as W
import Cubical.Data.FinData.Base as F
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.HITs.CauchyReals.Example.Financial.Examples.CommonScenarioData
  using (two; half; fair)
open import Cubical.HITs.CauchyReals.Example.Financial.Core.Vectors public using (four)

-- Leaf order is (branch 0, leaf 0), (0, 1), (1, 0), (1, 1).
-- Coupled model 0 selects leaf 0 at branch 0 and leaf 1 at branch 1.
-- Coupled model 1 selects the opposite two leaves. Both keep fair branches.
coupled0 coupled1 : Distribution 4
coupled0 = four half 0 0 half , positive , total
  where
  positive : ∀ i → 0 ≤ᵣ four half 0 0 half i
  positive F.zero = decℚ≤ᵣ?
  positive (F.suc F.zero) = decℚ≤ᵣ?
  positive (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  positive (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?
  total : sum (four half 0 0 half) ≡ 1
  total = ℝ!

coupled1 = four 0 half half 0 , positive , total
  where
  positive : ∀ i → 0 ≤ᵣ four 0 half half 0 i
  positive F.zero = decℚ≤ᵣ?
  positive (F.suc F.zero) = decℚ≤ᵣ?
  positive (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  positive (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?
  total : sum (four 0 half half 0) ≡ 1
  total = ℝ!

coupledModels : Fin 2 → Distribution 4
coupledModels F.zero = coupled0
coupledModels (F.suc F.zero) = coupled1

flatLoss : Vector 4
flatLoss = four 4 0 4 0

treeLoss : LossTree 2 2
treeLoss i = two 4 0

coupled-value : ∀ i → expectation (coupledModels i) flatLoss ≡ 2
coupled-value F.zero = ℝ!
coupled-value (F.suc F.zero) = ℝ!

coupled-risk-two : A.robustExpectation coupledModels flatLoss ≡ 2
coupled-risk-two = cong W.worstCase (funExt coupled-value)
  ∙ W.worstCase-constant {1} 2

-- Convexly mixing the two coupled global models still satisfies budget 2.
coupled-mixtures-budget-two : (weights : Distribution 2) →
  expectation (A.mixture weights coupledModels) flatLoss ≤ᵣ 2
coupled-mixtures-budget-two = A.models-bound→mixtures coupledModels flatLoss 2
  (λ i → ≡ᵣWeaken≤ᵣ _ _ (coupled-value i))

initialModels : Fin 1 → Distribution 2
initialModels i = fair

localModels : Fin 2 → Fin 2 → Distribution 2
localModels i j = A.dirac j

module Independent = Rectangular initialModels localModels

-- These branch-dependent selections reproduce the two coupled models.
coupledChoice : Fin 2 → Fin 2 → Fin 2
coupledChoice F.zero i = i
coupledChoice (F.suc F.zero) F.zero = F.suc F.zero
coupledChoice (F.suc F.zero) (F.suc F.zero) = F.zero

coupled-tree-agrees : ∀ i →
  Independent.selectedExpectation F.zero (coupledChoice i) treeLoss
    ≡ expectation (coupledModels i) flatLoss
coupled-tree-agrees F.zero = ℝ!
coupled-tree-agrees (F.suc F.zero) = ℝ!

-- The rectangular set additionally permits leaf 0 at BOTH branches.
-- Its expected loss is 4, and no leaf loss exceeds 4.
independent-value-four :
  Independent.selectedExpectation F.zero (λ _ → F.zero) treeLoss ≡ 4
independent-value-four = ℝ!

rectangular-risk-four : Independent.rootRisk treeLoss ≡ 4
rectangular-risk-four = isAntisym≤ᵣ _ _ upper-bound lower-bound
  where
  leaf-bound : ∀ i j → treeLoss i j ≤ᵣ 4
  leaf-bound i F.zero = decℚ≤ᵣ?
  leaf-bound i (F.suc F.zero) = decℚ≤ᵣ?

  upper-bound : Independent.rootRisk treeLoss ≤ᵣ 4
  upper-bound = isTrans≤≡ᵣ _ _ _
    (Independent.root-monotone treeLoss (λ _ _ → 4) leaf-bound)
    (Independent.root-constant 4)

  lower-bound : 4 ≤ᵣ Independent.rootRisk treeLoss
  lower-bound = isTrans≡≤ᵣ _ _ _ (sym independent-value-four)
    (Independent.selected-model-upper treeLoss F.zero (λ _ → F.zero))

strict-rectangular-gap :
  A.robustExpectation coupledModels flatLoss <ᵣ Independent.rootRisk treeLoss
strict-rectangular-gap =
  subst2 _<ᵣ_ (sym coupled-risk-two) (sym rectangular-risk-four) decℚ<ᵣ?

rectangular-budget-two-impossible : (Independent.rootRisk treeLoss ≤ᵣ 2) → ⊥
rectangular-budget-two-impossible bound = isIrrefl<ᵣ 4
  (isTrans≤<ᵣ 4 2 4 (subst (λ r → r ≤ᵣ 2) rectangular-risk-four bound) decℚ<ᵣ?)
