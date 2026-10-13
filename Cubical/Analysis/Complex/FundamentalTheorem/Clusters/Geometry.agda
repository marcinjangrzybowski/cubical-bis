module Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Geometry where

-- Strict finite diameter and positive separation have common rational
-- margins. Matching transfers them while preserving all multiplicities.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (equivFun)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Real.Base using (rat)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Modulus.Distance
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Finite

ConfigurationDiameterBelow : ∀ {n} → Vec ℂ n → ℚ₊ → Type₀
ConfigurationDiameterBelow {n} roots ε = ∀ (i j : Fin n) →
  distanceℂ (lookup i roots) (lookup j roots) <ℝ ⟦ ε ⟧₊

ConfigurationGap : ∀ {m n} → Vec ℂ m → Vec ℂ n → ℚ₊ → Type₀
ConfigurationGap {m} {n} roots roots′ gap = ∀ (i : Fin m) (j : Fin n) →
  ⟦ gap ⟧₊ ≤ℝ distanceℂ (lookup i roots) (lookup j roots′)

diameter-margin : ∀ {n} (roots : Vec ℂ n) ε → ConfigurationDiameterBelow roots ε →
  PT.∥ Σ[ η ∈ ℚ₊ ] (∀ i j → distanceℂ (lookup i roots) (lookup j roots) + ⟦ η ⟧₊ ≤ℝ ⟦ ε ⟧₊) ∥₁
diameter-margin {n} roots ε small = finite-common-radius₂ n n
  (λ i j η → distanceℂ (lookup i roots) (lookup j roots) + ⟦ η ⟧₊ ≤ℝ ⟦ ε ⟧₊)
  (λ i j δ η below bounded → ≤ℝ-trans
    (distanceℂ (lookup i roots) (lookup j roots) + ⟦ δ ⟧₊)
    (distanceℂ (lookup i roots) (lookup j roots) + ⟦ η ⟧₊) ⟦ ε ⟧₊
    (addPres≤L ⟦ δ ⟧₊ ⟦ η ⟧₊ (distanceℂ (lookup i roots) (lookup j roots))
      (radius-monotone δ η below)) bounded) small

apart-configurations-gap : ∀ {m n} (roots : Vec ℂ m) (roots′ : Vec ℂ n) →
  (∀ i j → 0ℝ <ℝ distanceℂ (lookup i roots) (lookup j roots′)) →
  PT.∥ Σ[ gap ∈ ℚ₊ ] ConfigurationGap roots roots′ gap ∥₁
apart-configurations-gap {m} {n} roots roots′ apart = finite-common-radius₂ m n
  (λ i j gap → ⟦ gap ⟧₊ ≤ℝ distanceℂ (lookup i roots) (lookup j roots′))
  (λ i j δ η below bounded → ≤ℝ-trans ⟦ δ ⟧₊ ⟦ η ⟧₊
    (distanceℂ (lookup i roots) (lookup j roots′)) (radius-monotone δ η below) bounded)
  (λ i j → PT.map (λ { (gap , bounded) → gap ,
    subst (_≤ℝ distanceℂ (lookup i roots) (lookup j roots′)) (addIdL ⟦ gap ⟧₊) bounded }) (apart i j))

opaque
  matching-diameter : ∀ {n} (centers roots : Vec ℂ n) ε η →
    (∀ i j → distanceℂ (lookup i centers) (lookup j centers) + ⟦ η ⟧₊ ≤ℝ ⟦ ε ⟧₊) →
    MatchingClose roots ((η /2₊) /2₊) centers → ConfigurationDiameterBelow roots ε
  matching-diameter centers roots ε η margin = PT.rec (isPropΠ2 λ i j →
    isProp<ℝ (distanceℂ (lookup i roots) (lookup j roots)) ⟦ ε ⟧₊)
    λ { (σ , close) i j → <≤ℝ-trans (distanceℂ (lookup i roots) (lookup j roots))
      (distanceℂ (lookup (equivFun σ i) centers) (lookup (equivFun σ j) centers) + ⟦ η ⟧₊) ⟦ ε ⟧₊
      (distanceℂ-perturb< (lookup i roots) (lookup j roots)
        (lookup (equivFun σ i) centers) (lookup (equivFun σ j) centers) η (close i) (close j))
      (margin (equivFun σ i) (equivFun σ j)) }

  matching-gap : ∀ {m n} (centers : Vec ℂ m) (centers′ : Vec ℂ n) gap η →
    (∀ i j → ⟦ gap ⟧₊ + ⟦ η ⟧₊ ≤ℝ distanceℂ (lookup i centers) (lookup j centers′)) →
    ∀ (roots : Vec ℂ m) (roots′ : Vec ℂ n) →
    MatchingClose roots ((η /2₊) /2₊) centers →
    MatchingClose roots′ ((η /2₊) /2₊) centers′ → ConfigurationGap roots roots′ gap
  matching-gap centers centers′ gap η margin roots roots′ = PT.rec2
    (isPropΠ2 λ i j → isProp≤ℝ ⟦ gap ⟧₊ (distanceℂ (lookup i roots) (lookup j roots′)))
    λ { (σ , first) (τ , second) i j → <ℝ-weaken ⟦ gap ⟧₊ (distanceℂ (lookup i roots) (lookup j roots′))
      (<ℝ-addR-cancel ⟦ gap ⟧₊ (distanceℂ (lookup i roots) (lookup j roots′)) ⟦ η ⟧₊
        (≤<ℝ-trans (⟦ gap ⟧₊ + ⟦ η ⟧₊)
          (distanceℂ (lookup (equivFun σ i) centers) (lookup (equivFun τ j) centers′))
          (distanceℂ (lookup i roots) (lookup j roots′) + ⟦ η ⟧₊)
          (margin (equivFun σ i) (equivFun τ j))
          (distanceℂ-perturb< (lookup (equivFun σ i) centers) (lookup (equivFun τ j) centers′)
            (lookup i roots) (lookup j roots′) η
            (sym∼ℂ (lookup i roots) (lookup (equivFun σ i) centers) ((η /2₊) /2₊) (first i))
            (sym∼ℂ (lookup j roots′) (lookup (equivFun τ j) centers′) ((η /2₊) /2₊) (second j))))) }
