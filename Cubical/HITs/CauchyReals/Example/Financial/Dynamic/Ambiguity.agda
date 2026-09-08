module Cubical.HITs.CauchyReals.Example.Financial.Dynamic.Ambiguity where

open import Cubical.HITs.CauchyReals.Example.Financial.Dynamic.Base public
import Cubical.HITs.CauchyReals.Example.Financial.Risk.Ambiguity as A
import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase as W
import Cubical.Data.FinData.Base as F
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- Finite model ambiguity supplies a coherent local risk rule. Every law
-- is already proved for arbitrary Cauchy-real scenario probabilities.
robustRisk : ∀ {k n} → (Fin (suc k) → Distribution n) → CoherentRisk n
robustRisk models .evaluate = A.robustExpectation models
robustRisk models .monotone = A.robust-monotone models
robustRisk models .cash = A.robust-cash models
robustRisk models .homogeneous a X a₊ = A.robust-scale models X a a₊
robustRisk models .subadditive = A.robust-subadditive models

-- Rectangular ambiguity allows a separate conditional mixture at each
-- observed branch. A single common latent model index would be a smaller,
-- coupled ambiguity set, which is deliberately not identified with this one.
module Rectangular {k l m n : ℕ}
  (outerModels : Fin (suc k) → Distribution m)
  (innerModels : Fin m → Fin (suc l) → Distribution n) where

  module Evaluation = TwoStage (robustRisk outerModels)
    (λ i → robustRisk (innerModels i))

  open Evaluation public

  rectangularExpectation : Distribution (suc k)
    → (Fin m → Distribution (suc l)) → LossTree m n → ℝ
  rectangularExpectation outerWeights innerWeights X =
    expectation (A.mixture outerWeights outerModels)
      (λ i → expectation (A.mixture (innerWeights i) (innerModels i)) (X i))

  -- Any real-valued convex mixture of the initial models is allowed, and
  -- each branch may independently use any convex mixture of its local models.
  -- The proof uses upper bounds only; it never chooses a maximizing model.
  rectangular-mixture-upper : (X : LossTree m n)
    (outerWeights : Distribution (suc k))
    (innerWeights : Fin m → Distribution (suc l)) →
    rectangularExpectation outerWeights innerWeights X ≤ᵣ rootRisk X
  rectangular-mixture-upper X outerWeights innerWeights = isTrans≤ᵣ _ _ _
    (expectation-monotone (A.mixture outerWeights outerModels)
      (λ i → expectation (A.mixture (innerWeights i) (innerModels i)) (X i))
      (continuationRisk X)
      (λ i → A.robust-mixture-upper (innerModels i) (X i) (innerWeights i)))
    (A.robust-mixture-upper outerModels (continuationRisk X) outerWeights)

  rectangular-budget-sound : (X : LossTree m n) (cap : ℝ) →
    rootRisk X ≤ᵣ cap → (outerWeights : Distribution (suc k))
    (innerWeights : Fin m → Distribution (suc l)) →
    rectangularExpectation outerWeights innerWeights X ≤ᵣ cap
  rectangular-budget-sound X cap bound outerWeights innerWeights =
    isTrans≤ᵣ _ _ _ (rectangular-mixture-upper X outerWeights innerWeights) bound

  -- Explicit node-budget certificates have the same guarantee for every
  -- rectangular mixture. A local manager need only meet its allocated bound.
  node-budget-mixture-sound : (X : LossTree m n) (cap : ℝ) →
    NodeBudgetCertificate X cap → (outerWeights : Distribution (suc k))
    (innerWeights : Fin m → Distribution (suc l)) →
    rectangularExpectation outerWeights innerWeights X ≤ᵣ cap
  node-budget-mixture-sound X cap certificate =
    rectangular-budget-sound X cap (node-certificate-sound X cap certificate)

  selectedExpectation : Fin (suc k) → (Fin m → Fin (suc l)) → LossTree m n → ℝ
  selectedExpectation outerIndex select X = expectation (outerModels outerIndex)
    (λ i → expectation (innerModels i (select i)) (X i))

  selected-model-upper : (X : LossTree m n) (outerIndex : Fin (suc k))
    (select : Fin m → Fin (suc l)) →
    selectedExpectation outerIndex select X ≤ᵣ rootRisk X
  selected-model-upper X outerIndex select = isTrans≤ᵣ _ _ _
    (expectation-monotone (outerModels outerIndex)
      (λ i → expectation (innerModels i (select i)) (X i))
      (continuationRisk X) (λ i → A.robust-upper (innerModels i) (X i) (select i)))
    (A.robust-upper outerModels (continuationRisk X) outerIndex)

  -- The same expectation can be evaluated directly using joint leaf
  -- probabilities, by the finite conditional-expectation tower theorem.
  rectangular-tower : (X : LossTree m n)
    (outerWeights : Distribution (suc k))
    (innerWeights : Fin m → Distribution (suc l)) →
    rectangularExpectation outerWeights innerWeights X
    ≡ sum (λ i → sum (λ j →
      jointMass (A.mixture outerWeights outerModels)
        (λ i → A.mixture (innerWeights i) (innerModels i)) i j ·ᵣ X i j))
  rectangular-tower X outerWeights innerWeights =
    expectation-tower (A.mixture outerWeights outerModels)
      (λ i → A.mixture (innerWeights i) (innerModels i)) X
