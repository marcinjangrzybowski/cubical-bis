module Cubical.Analysis.Complex.FundamentalTheorem.Completion.Bounds where

-- Matching transfers a root bound to every root on the other side.
-- Using the inverse permutation is essential: multiplicities and all
-- target indices are covered, without selecting or comparing root values.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (_≃_; equivFun; invEq; secEq)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Polynomial.Newton.Remainder using (normℂ-ballBound)
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Perturbation

opaque
  matching-nearby-bound : ∀ {n} (xs ys : Vec ℂ n) B r →
    RootsBounded xs B → MatchingClose xs r ys → RootsBounded ys (B +₊ (r +₊ r))
  matching-nearby-bound {n} xs ys B r bounded = PT.rec
    (isPropΠ λ i → isProp≤ℝ (normℂ (lookup i ys)) ⟦ B +₊ (r +₊ r) ⟧₊)
    matched
    where
    matched : (Σ[ σ ∈ (Fin n ≃ Fin n) ]
      (∀ i → lookup i xs ∼ℂ[ r ] lookup (equivFun σ i) ys)) →
      RootsBounded ys (B +₊ (r +₊ r))
    matched (σ , close) j = subst (λ k → normℂ (lookup k ys) ≤ℝ ⟦ B +₊ (r +₊ r) ⟧₊)
      (secEq σ j)
      (subst (normℂ (lookup (equivFun σ (invEq σ j)) ys) ≤ℝ_)
        (cong (⟦ B ⟧₊ +_) (rat+rat (fst r) (fst r)) ∙ rat+rat (fst B) (fst (r +₊ r)))
        (normℂ-ballBound (lookup (invEq σ j) xs) ⟦ B ⟧₊ (⟦ r ⟧₊ + ⟦ r ⟧₊)
          (lookup (equivFun σ (invEq σ j)) ys) (bounded (invEq σ j))
          (closeness→differenceBound (lookup (equivFun σ (invEq σ j)) ys) (lookup (invEq σ j) xs) r
            (sym∼ℂ (lookup (invEq σ j) xs) (lookup (equivFun σ (invEq σ j)) ys) r (close (invEq σ j))))))
