module Cubical.HITs.CauchyReals.Example.Financial.Dynamic.Base where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Probability public
import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase as W
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.FinData.Base as F
import Cubical.HITs.PropositionalTruncation as PT

-- A local capital rule, in loss convention. The scaling law includes zero;
-- normalization and evaluation of deterministic losses follow from the laws.
record CoherentRisk (n : ℕ) : Type₀ where
  field
    evaluate : Vector n → ℝ
    monotone : (X Y : Vector n) → (∀ i → X i ≤ᵣ Y i) → evaluate X ≤ᵣ evaluate Y
    cash : (X : Vector n) (c : ℝ) →
      evaluate (λ i → X i +ᵣ c) ≡ evaluate X +ᵣ c
    homogeneous : (a : ℝ) (X : Vector n) → 0 ≤ᵣ a →
      evaluate (λ i → a ·ᵣ X i) ≡ a ·ᵣ evaluate X
    subadditive : (X Y : Vector n) →
      evaluate (λ i → X i +ᵣ Y i) ≤ᵣ evaluate X +ᵣ evaluate Y

open CoherentRisk public

risk-zero : ∀ {n} (R : CoherentRisk n) → evaluate R (λ _ → 0) ≡ 0
risk-zero R =
  sym (cong (evaluate R) (funExt (λ _ → Rℝ.0LeftAnnihilates 0)))
  ∙ homogeneous R 0 (λ _ → 0) (≤ᵣ-refl 0)
  ∙ Rℝ.0LeftAnnihilates (evaluate R (λ _ → 0))

risk-constant : ∀ {n} (R : CoherentRisk n) c → evaluate R (λ _ → c) ≡ c
risk-constant R c =
  sym (cong (evaluate R) (funExt (λ _ → +IdL c)))
  ∙ cash R (λ _ → 0) c
  ∙ cong (_+ᵣ c) (risk-zero R) ∙ +IdL c

expectationRisk : ∀ {n} → Distribution n → CoherentRisk n
expectationRisk P .evaluate = expectation P
expectationRisk P .monotone = expectation-monotone P
expectationRisk P .cash = expectation-cash P
expectationRisk P .homogeneous a X a₊ = expectation-scale P a X
expectationRisk P .subadditive X Y =
  ≡ᵣWeaken≤ᵣ _ _ (expectation-add P X Y)

worstCaseRisk : ∀ {n} → CoherentRisk (suc n)
worstCaseRisk .evaluate = W.worstCase
worstCaseRisk .monotone = W.worstCase-monotone
worstCaseRisk .cash = W.worstCase-cash
worstCaseRisk .homogeneous a X a₊ = W.worstCase-scale X a a₊
worstCaseRisk .subadditive = W.worstCase-subadditive

LossTree : ℕ → ℕ → Type₀
LossTree m n = Fin m → Vector n

-- First a branch is observed; then a leaf is observed. Local risk rules may
-- differ by branch. Backward evaluation is a management rule in its own
-- right: no assertion identifies it with an arbitrary static tail-risk rule.
module TwoStage {m n : ℕ}
  (outer : CoherentRisk m) (inner : Fin m → CoherentRisk n) where

  continuationRisk : LossTree m n → Vector m
  continuationRisk X i = evaluate (inner i) (X i)

  rootRisk : LossTree m n → ℝ
  rootRisk X = evaluate outer (continuationRisk X)

  -- Strong time consistency compares the conditional risk assessments.
  -- It does not require one policy to dominate the other at every leaf.
  strong-time-consistency : (X Y : LossTree m n) →
    (∀ i → continuationRisk X i ≤ᵣ continuationRisk Y i) → rootRisk X ≤ᵣ rootRisk Y
  strong-time-consistency X Y = monotone outer (continuationRisk X) (continuationRisk Y)

  root-monotone : (X Y : LossTree m n) →
    (∀ i j → X i j ≤ᵣ Y i j) → rootRisk X ≤ᵣ rootRisk Y
  root-monotone X Y bound = strong-time-consistency X Y
    (λ i → monotone (inner i) (X i) (Y i) (bound i))

  root-cash : (X : LossTree m n) (c : ℝ) →
    rootRisk (λ i j → X i j +ᵣ c) ≡ rootRisk X +ᵣ c
  root-cash X c =
    cong (evaluate outer) (funExt (λ i → cash (inner i) (X i) c))
    ∙ cash outer (continuationRisk X) c

  root-homogeneous : (a : ℝ) (X : LossTree m n) → 0 ≤ᵣ a →
    rootRisk (λ i j → a ·ᵣ X i j) ≡ a ·ᵣ rootRisk X
  root-homogeneous a X a₊ =
    cong (evaluate outer) (funExt (λ i → homogeneous (inner i) a (X i) a₊))
    ∙ homogeneous outer a (continuationRisk X) a₊

  root-subadditive : (X Y : LossTree m n) →
    rootRisk (λ i j → X i j +ᵣ Y i j) ≤ᵣ rootRisk X +ᵣ rootRisk Y
  root-subadditive X Y = isTrans≤ᵣ _ _ _
    (monotone outer (continuationRisk (λ i j → X i j +ᵣ Y i j))
      (λ i → continuationRisk X i +ᵣ continuationRisk Y i)
      (λ i → subadditive (inner i) (X i) (Y i)))
    (subadditive outer (continuationRisk X) (continuationRisk Y))

  root-constant : (c : ℝ) → rootRisk (λ _ _ → c) ≡ c
  root-constant c =
    cong (evaluate outer) (funExt (λ i → risk-constant (inner i) c))
    ∙ risk-constant outer c

  -- Allocate a branch budget B i after the first observation. The root
  -- capital required by these budgets is evaluate outer B.
  nodewise-budgets : (X : LossTree m n) (B : Vector m) →
    (∀ i → continuationRisk X i ≤ᵣ B i) → rootRisk X ≤ᵣ evaluate outer B
  nodewise-budgets X B = monotone outer (continuationRisk X) B

  budget-propagation : (X : LossTree m n) (B : Vector m) (cap : ℝ) →
    (∀ i → continuationRisk X i ≤ᵣ B i) → evaluate outer B ≤ᵣ cap → rootRisk X ≤ᵣ cap
  budget-propagation X B cap local aggregate =
    isTrans≤ᵣ _ _ _ (nodewise-budgets X B local) aggregate

  uniform-nodewise-budget : (X : LossTree m n) (cap : ℝ) →
    (∀ i → continuationRisk X i ≤ᵣ cap) → rootRisk X ≤ᵣ cap
  uniform-nodewise-budget X cap local =
    isTrans≤≡ᵣ _ _ _ (nodewise-budgets X (λ _ → cap) local)
      (risk-constant outer cap)

  -- A certificate records the intermediate capital allocation, so a local
  -- manager can check its own branch obligation independently.
  NodeBudgetCertificate : LossTree m n → ℝ → Type₀
  NodeBudgetCertificate X cap = Σ[ B ∈ Vector m ]
    ((∀ i → continuationRisk X i ≤ᵣ B i) × (evaluate outer B ≤ᵣ cap))

  node-certificate-sound : (X : LossTree m n) (cap : ℝ) →
    NodeBudgetCertificate X cap → rootRisk X ≤ᵣ cap
  node-certificate-sound X cap (B , local , aggregate) =
    budget-propagation X B cap local aggregate

  node-certificate-complete : (X : LossTree m n) (cap : ℝ) →
    rootRisk X ≤ᵣ cap → NodeBudgetCertificate X cap
  node-certificate-complete X cap bound =
    continuationRisk X , (λ i → ≤ᵣ-refl _) , bound

  -- Hiding the particular allocation yields precisely root acceptance.
  -- Propositional truncation hides witnesses without requiring any choice.
  node-certificates≃root-budget : (X : LossTree m n) (cap : ℝ) →
    PT.∥ NodeBudgetCertificate X cap ∥₁ ≃ (rootRisk X ≤ᵣ cap)
  node-certificates≃root-budget X cap = propBiimpl→Equiv
    PT.squash₁ (isProp≤ᵣ _ _)
    (PT.rec (isProp≤ᵣ _ _) (node-certificate-sound X cap))
    (λ bound → PT.∣ node-certificate-complete X cap bound ∣₁)

  -- A known payment at an intermediate node can be added after its local
  -- future risk is computed; it need not be repeated in every leaf.
  stage-cost-recursion : (X : LossTree m n) (cost : Vector m) →
    rootRisk (λ i j → X i j +ᵣ cost i)
      ≡ evaluate outer (λ i → continuationRisk X i +ᵣ cost i)
  stage-cost-recursion X cost =
    cong (evaluate outer) (funExt (λ i → cash (inner i) (X i) (cost i)))

  -- Nonuniform errors in branch risk certificates accumulate through the
  -- outer capital rule. This also allows negative errors (improvements).
  branch-perturbation : (X Y : LossTree m n) (errors : Vector m) →
    (∀ i → continuationRisk X i ≤ᵣ continuationRisk Y i +ᵣ errors i) →
    rootRisk X ≤ᵣ rootRisk Y +ᵣ evaluate outer errors
  branch-perturbation X Y errors bound = isTrans≤ᵣ _ _ _
    (monotone outer (continuationRisk X)
      (λ i → continuationRisk Y i +ᵣ errors i) bound)
    (subadditive outer (continuationRisk Y) errors)

-- Bellman's maximum principle without selecting a maximizing leaf. This
-- universal property is the maximum over the complete rectangular tree.
nestedWorstCase : ∀ {m n} → LossTree (suc m) (suc n) → ℝ
nestedWorstCase X = W.worstCase (λ i → W.worstCase (X i))

nestedWorstCase-upper : ∀ {m n} (X : LossTree (suc m) (suc n)) i j →
  X i j ≤ᵣ nestedWorstCase X
nestedWorstCase-upper X i j = isTrans≤ᵣ _ _ _
  (W.worstCase-upper (X i) j) (W.worstCase-upper (λ k → W.worstCase (X k)) i)

nestedWorstCase-least : ∀ {m n} (X : LossTree (suc m) (suc n)) cap →
  (∀ i j → X i j ≤ᵣ cap) → nestedWorstCase X ≤ᵣ cap
nestedWorstCase-least X cap bound = W.worstCase-least
  (λ i → W.worstCase (X i)) cap (λ i → W.worstCase-least (X i) cap (bound i))

nestedWorstCase-budget≃leaves : ∀ {m n} (X : LossTree (suc m) (suc n)) cap →
  (nestedWorstCase X ≤ᵣ cap) ≃ (∀ i j → X i j ≤ᵣ cap)
nestedWorstCase-budget≃leaves X cap = propBiimpl→Equiv
  (isProp≤ᵣ _ _) (isPropΠ2 (λ _ _ → isProp≤ᵣ _ _))
  (λ bound i j → isTrans≤ᵣ _ _ _ (nestedWorstCase-upper X i j) bound)
  (nestedWorstCase-least X cap)

nestedWorstCase-budget-path : ∀ {m n} (X : LossTree (suc m) (suc n)) cap →
  (nestedWorstCase X ≤ᵣ cap) ≡ (∀ i j → X i j ≤ᵣ cap)
nestedWorstCase-budget-path X cap = ua (nestedWorstCase-budget≃leaves X cap)

nestedWorstCase-interchange : ∀ {m n} (X : LossTree (suc m) (suc n)) →
  nestedWorstCase X ≡ nestedWorstCase (λ j i → X i j)
nestedWorstCase-interchange X = isAntisym≤ᵣ _ _
  (nestedWorstCase-least X _ (λ i j → nestedWorstCase-upper (λ j i → X i j) j i))
  (nestedWorstCase-least (λ j i → X i j) _ (λ j i → nestedWorstCase-upper X i j))

-- Multiplying first-stage and conditional probabilities gives total mass
-- one. The tower formula is a finite calculation, including zero atoms.
jointMass : ∀ {m n} → Distribution m → (Fin m → Distribution n) → LossTree m n
jointMass P Q i j = probability P i ·ᵣ probability (Q i) j

jointMass-total : ∀ {m n} (P : Distribution m) (Q : Fin m → Distribution n) →
  sum (λ i → sum (jointMass P Q i)) ≡ 1
jointMass-total P Q =
  sum-cong (λ i → sum (jointMass P Q i)) (probability P)
    (λ i → sum-scale (probability P i) (probability (Q i))
      ∙ cong (probability P i ·ᵣ_) (probability-total (Q i))
      ∙ ·IdR (probability P i))
  ∙ probability-total P

expectation-tower : ∀ {m n} (P : Distribution m) (Q : Fin m → Distribution n)
  (X : LossTree m n) →
  TwoStage.rootRisk (expectationRisk P) (λ i → expectationRisk (Q i)) X
    ≡ sum (λ i → sum (λ j → jointMass P Q i j ·ᵣ X i j))
expectation-tower P Q X = sum-cong
  (λ i → probability P i ·ᵣ sum (λ j → probability (Q i) j ·ᵣ X i j))
  (λ i → sum (λ j → jointMass P Q i j ·ᵣ X i j))
  (λ i → sym (sum-scale (probability P i) (λ j → probability (Q i) j ·ᵣ X i j))
    ∙ sum-cong
      (λ j → probability P i ·ᵣ (probability (Q i) j ·ᵣ X i j))
      (λ j → jointMass P Q i j ·ᵣ X i j)
      (λ j → ·ᵣAssoc (probability P i) (probability (Q i) j) (X i j)))
