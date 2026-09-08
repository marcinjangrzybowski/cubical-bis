{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Risk.Ambiguity where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Probability public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (ua)
import Cubical.Data.FinData.Base as F
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- Concentrating probability at a data-finite index needs only structural
-- recursion on indices; it does not compare or select any real numbers.
pointMass : ∀ {n} → Fin n → Vector n
pointMass F.zero F.zero = 1
pointMass F.zero (F.suc j) = 0
pointMass (F.suc i) F.zero = 0
pointMass (F.suc i) (F.suc j) = pointMass i j

pointMass-nonnegative : ∀ {n} (i j : Fin n) → 0 ≤ᵣ pointMass i j
pointMass-nonnegative F.zero F.zero = decℚ≤ᵣ?
pointMass-nonnegative F.zero (F.suc j) = ≤ᵣ-refl 0
pointMass-nonnegative (F.suc i) F.zero = ≤ᵣ-refl 0
pointMass-nonnegative (F.suc i) (F.suc j) = pointMass-nonnegative i j

pointMass-total : ∀ {n} (i : Fin n) → sum (pointMass i) ≡ 1
pointMass-total {suc n} F.zero = cong (1 +ᵣ_) (sum-zero n) ∙ +IdR 1
pointMass-total {suc n} (F.suc i) =
  cong (0 +ᵣ_) (pointMass-total i) ∙ +IdL 1

dirac : ∀ {n} → Fin n → Distribution n
dirac i = pointMass i , pointMass-nonnegative i , pointMass-total i

expectation-dirac : ∀ {n} (i : Fin n) (X : Vector n) →
  expectation (dirac i) X ≡ X i
expectation-dirac {suc n} F.zero X =
  cong₂ _+ᵣ_ (·IdLᵣ (X F.zero))
    (sum-cong _ _ (λ j → Rℝ.0LeftAnnihilates (X (F.suc j))) ∙ sum-zero n)
  ∙ +IdR (X F.zero)
expectation-dirac {suc n} (F.suc i) X =
  cong₂ _+ᵣ_ (Rℝ.0LeftAnnihilates (X F.zero))
    (expectation-dirac i (λ j → X (F.suc j))) ∙ +IdL (X (F.suc i))

-- A distribution of model weights mixes finitely many scenario laws.
-- Both weights and model probabilities may be arbitrary Cauchy reals.
mixture : ∀ {k n} → Distribution k → (Fin k → Distribution n) → Distribution n
mixture W models = probabilities , nonnegative , total
  where
  probabilities : Vector _
  probabilities j = expectation W (λ i → probability (models i) j)

  nonnegative : ∀ j → 0 ≤ᵣ probabilities j
  nonnegative j = expectation-nonnegative W _
    (λ i → probability-nonnegative (models i) j)

  total : sum probabilities ≡ 1
  total = sum-exchange (λ j i → probability W i ·ᵣ probability (models i) j)
    ∙ sum-cong _ _ (λ i → sum-scale (probability W i) (probability (models i))
      ∙ cong (probability W i ·ᵣ_) (probability-total (models i))
      ∙ ·IdR (probability W i))
    ∙ probability-total W

private
  sum-scale-right : ∀ {n} (X : Vector n) a →
    sum (λ i → X i ·ᵣ a) ≡ sum X ·ᵣ a
  sum-scale-right X a = sum-cong _ _ (λ i → ·ᵣComm (X i) a)
    ∙ sum-scale a X ∙ ·ᵣComm a (sum X)

-- Finite Fubini: averaging scenario losses after mixing models equals
-- averaging the model expectations with the same mixing probabilities.
expectation-mixture : ∀ {k n} (W : Distribution k)
  (models : Fin k → Distribution n) (X : Vector n) →
  expectation (mixture W models) X ≡ expectation W (λ i → expectation (models i) X)
expectation-mixture W models X =
  sum-cong _ _ (λ j → sym (sum-scale-right
    (λ i → probability W i ·ᵣ probability (models i) j) (X j)))
  ∙ sum-exchange (λ j i → (probability W i ·ᵣ probability (models i) j) ·ᵣ X j)
  ∙ sum-cong _ _ (λ i →
    sum-cong _ _ (λ j → sym (·ᵣAssoc (probability W i) (probability (models i) j) (X j)))
    ∙ sum-scale (probability W i) (λ j → probability (models i) j ·ᵣ X j))

-- Distribution equality ignores the proofs of normalization and positivity.
mixture-dirac : ∀ {k n} (models : Fin k → Distribution n) (i : Fin k) →
  mixture (dirac i) models ≡ models i
mixture-dirac models i = distribution-path
  (λ j → expectation-dirac i (λ k → probability (models k) j))

-- Risk under finite probability ambiguity is the largest expected loss.
-- Nonempty model lists preserve guaranteed gains and exact cash additivity.
robustExpectation : ∀ {k n} → (Fin (suc k) → Distribution n) → Vector n → ℝ
robustExpectation models X = worstCase (λ i → expectation (models i) X)

robust-upper : ∀ {k n} (models : Fin (suc k) → Distribution n) X i →
  expectation (models i) X ≤ᵣ robustExpectation models X
robust-upper models X = worstCase-upper (λ i → expectation (models i) X)

robust-least : ∀ {k n} (models : Fin (suc k) → Distribution n) X budget →
  (∀ i → expectation (models i) X ≤ᵣ budget) → robustExpectation models X ≤ᵣ budget
robust-least models X = worstCase-least (λ i → expectation (models i) X)

robust-monotone : ∀ {k n} (models : Fin (suc k) → Distribution n) X Y →
  (∀ j → X j ≤ᵣ Y j) → robustExpectation models X ≤ᵣ robustExpectation models Y
robust-monotone models X Y bound = worstCase-monotone _ _
  (λ i → expectation-monotone (models i) X Y bound)

robust-constant : ∀ {k n} (models : Fin (suc k) → Distribution n) c →
  robustExpectation models (λ _ → c) ≡ c
robust-constant {k} models c =
  cong worstCase (funExt (λ i → expectation-constant (models i) c))
  ∙ worstCase-constant {k} c

robust-cash : ∀ {k n} (models : Fin (suc k) → Distribution n) X c →
  robustExpectation models (λ j → X j +ᵣ c) ≡ robustExpectation models X +ᵣ c
robust-cash models X c =
  cong worstCase (funExt (λ i → expectation-cash (models i) X c))
  ∙ worstCase-cash (λ i → expectation (models i) X) c

robust-scale : ∀ {k n} (models : Fin (suc k) → Distribution n) X a → 0 ≤ᵣ a →
  robustExpectation models (λ j → a ·ᵣ X j) ≡ a ·ᵣ robustExpectation models X
robust-scale models X a a₊ =
  cong worstCase (funExt (λ i → expectation-scale (models i) a X))
  ∙ worstCase-scale (λ i → expectation (models i) X) a a₊

robust-subadditive : ∀ {k n} (models : Fin (suc k) → Distribution n) X Y →
  robustExpectation models (λ j → X j +ᵣ Y j)
    ≤ᵣ robustExpectation models X +ᵣ robustExpectation models Y
robust-subadditive models X Y = isTrans≡≤ᵣ _ _ _
  (cong worstCase (funExt (λ i → expectation-add (models i) X Y)))
  (worstCase-subadditive (λ i → expectation (models i) X) (λ i → expectation (models i) Y))

robust-weighted : ∀ {k n} (models : Fin (suc k) → Distribution n) X Y a b →
  0 ≤ᵣ a → 0 ≤ᵣ b →
  robustExpectation models (λ j → a ·ᵣ X j +ᵣ b ·ᵣ Y j)
    ≤ᵣ a ·ᵣ robustExpectation models X +ᵣ b ·ᵣ robustExpectation models Y
robust-weighted models X Y a b a₊ b₊ = isTrans≡≤ᵣ _ _ _
  (cong worstCase (funExt (λ i →
    expectation-add (models i) (λ j → a ·ᵣ X j) (λ j → b ·ᵣ Y j)
    ∙ cong₂ _+ᵣ_ (expectation-scale (models i) a X) (expectation-scale (models i) b Y))))
  (worstCase-weighted (λ i → expectation (models i) X) (λ i → expectation (models i) Y) a b a₊ b₊)

robust-perturbation : ∀ {k n} (models : Fin (suc k) → Distribution n) X Y ε →
  (∀ j → X j ≤ᵣ Y j +ᵣ ε) →
  robustExpectation models X ≤ᵣ robustExpectation models Y +ᵣ ε
robust-perturbation models X Y ε bound = worstCase-perturbation _ _ ε
  (λ i → expectation-perturbation (models i) X Y ε bound)

robust-budget≃models : ∀ {k n} (models : Fin (suc k) → Distribution n) X budget →
  (robustExpectation models X ≤ᵣ budget) ≃
  (∀ i → expectation (models i) X ≤ᵣ budget)
robust-budget≃models models X budget = worstCase-budget≃pointwise _ budget

models-bound→mixtures : ∀ {k n} (models : Fin k → Distribution n) X budget →
  (∀ i → expectation (models i) X ≤ᵣ budget) →
  (W : Distribution k) → expectation (mixture W models) X ≤ᵣ budget
models-bound→mixtures models X budget bound W = isTrans≡≤ᵣ _ _ _
  (expectation-mixture W models X)
  (isTrans≤≡ᵣ _ _ _ (expectation-monotone W _ (λ _ → budget) bound)
    (expectation-constant W budget))

mixtures-bound→models : ∀ {k n} (models : Fin k → Distribution n) X budget →
  ((W : Distribution k) → expectation (mixture W models) X ≤ᵣ budget) →
  ∀ i → expectation (models i) X ≤ᵣ budget
mixtures-bound→models models X budget bound i = isTrans≡≤ᵣ _ _ _
  (sym (cong (λ P → expectation P X) (mixture-dirac models i))) (bound (dirac i))

-- Testing all extreme models is exactly testing their whole convex hull,
-- with arbitrary real weights; the backward direction uses Dirac weights.
models-budget≃mixtures : ∀ {k n} (models : Fin k → Distribution n) X budget →
  (∀ i → expectation (models i) X ≤ᵣ budget) ≃
  ((W : Distribution k) → expectation (mixture W models) X ≤ᵣ budget)
models-budget≃mixtures models X budget = propBiimpl→Equiv
  (isPropΠ (λ _ → isProp≤ᵣ _ _)) (isPropΠ (λ _ → isProp≤ᵣ _ _))
  (models-bound→mixtures models X budget) (mixtures-bound→models models X budget)

robust-budget≃mixtures : ∀ {k n} (models : Fin (suc k) → Distribution n) X budget →
  (robustExpectation models X ≤ᵣ budget) ≃
  ((W : Distribution (suc k)) → expectation (mixture W models) X ≤ᵣ budget)
robust-budget≃mixtures models X budget = compEquiv
  (robust-budget≃models models X budget) (models-budget≃mixtures models X budget)

robust-policy-path : ∀ {k n} (models : Fin (suc k) → Distribution n) X budget →
  (robustExpectation models X ≤ᵣ budget) ≡
  ((W : Distribution (suc k)) → expectation (mixture W models) X ≤ᵣ budget)
robust-policy-path models X budget = ua (robust-budget≃mixtures models X budget)

robust-mixture-upper : ∀ {k n} (models : Fin (suc k) → Distribution n) X
  (W : Distribution (suc k)) →
  expectation (mixture W models) X ≤ᵣ robustExpectation models X
robust-mixture-upper models X = models-bound→mixtures models X _ (robust-upper models X)

-- The same guarantee covers finite selections of any size, including
-- repeated models. Thus the policy does not depend on an enumeration of
-- the generators used by a downstream mixing procedure.
AllFiniteMixturesBound : ∀ {k n} (models : Fin k → Distribution n) →
  Vector n → ℝ → Type₀
AllFiniteMixturesBound models X budget =
  ∀ m (select : Fin m → Fin _) (W : Distribution m) →
    expectation (mixture W (λ i → models (select i))) X ≤ᵣ budget

models-bound→finite-mixtures : ∀ {k n} (models : Fin k → Distribution n) X budget →
  (∀ i → expectation (models i) X ≤ᵣ budget) → AllFiniteMixturesBound models X budget
models-bound→finite-mixtures models X budget bound m select =
  models-bound→mixtures (λ i → models (select i)) X budget (λ i → bound (select i))

finite-mixtures-bound→models : ∀ {k n} (models : Fin k → Distribution n) X budget →
  AllFiniteMixturesBound models X budget → ∀ i → expectation (models i) X ≤ᵣ budget
finite-mixtures-bound→models models X budget bound i = isTrans≡≤ᵣ _ _ _
  (sym (cong (λ P → expectation P X)
    (mixture-dirac (λ (_ : Fin 1) → models i) F.zero)))
  (bound 1 (λ _ → i) (dirac F.zero))

models-budget≃finite-mixtures : ∀ {k n} (models : Fin k → Distribution n) X budget →
  (∀ i → expectation (models i) X ≤ᵣ budget) ≃ AllFiniteMixturesBound models X budget
models-budget≃finite-mixtures models X budget = propBiimpl→Equiv
  (isPropΠ (λ _ → isProp≤ᵣ _ _))
  (isPropΠ (λ _ → isPropΠ (λ _ → isPropΠ (λ _ → isProp≤ᵣ _ _))))
  (models-bound→finite-mixtures models X budget)
  (finite-mixtures-bound→models models X budget)

robust-budget≃finite-mixtures : ∀ {k n} (models : Fin (suc k) → Distribution n) X budget →
  (robustExpectation models X ≤ᵣ budget) ≃ AllFiniteMixturesBound models X budget
robust-budget≃finite-mixtures models X budget = compEquiv
  (robust-budget≃models models X budget) (models-budget≃finite-mixtures models X budget)
