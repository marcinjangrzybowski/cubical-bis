module Cubical.Analysis.Complex.Calculus.Derivative.Tower.OpenSubspace where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Tower
open import Cubical.Analysis.Complex.Calculus.Derivative.OpenSubspace.Uniqueness

-- Local derivative towers are determined by their order-zero function.
-- No ambient extensions of the tower functions are required.
opaque
  openSubspaceComplexDerivativeTowerUnique : ∀ (P : ℙ ℂ) →
    IsOpenPredicate (ℂPremetricSpace .snd) P →
    ∀ (first second : ℕ → fst (PremetricSubspace ℂPremetricSpace P) → ℂ) →
    IsComplexDerivativeTowerAlong (PremetricSubspace ℂPremetricSpace P .snd) fst first →
    IsComplexDerivativeTowerAlong (PremetricSubspace ℂPremetricSpace P .snd) fst second →
    first zero ≡ second zero → first ≡ second
  openSubspaceComplexDerivativeTowerUnique P openP first second firstTower secondTower base = funExt equal
    where
    equal : ∀ n → first n ≡ second n
    equal zero = base
    equal (suc n) = openSubspaceComplexDerivativeFunctionUnique P openP
      (first n) (first (suc n)) (second (suc n)) (firstTower n)
      (subst (λ f → IsComplexDerivativeAlong (PremetricSubspace ℂPremetricSpace P .snd) fst f (second (suc n)))
        (sym (equal n)) (secondTower n))
