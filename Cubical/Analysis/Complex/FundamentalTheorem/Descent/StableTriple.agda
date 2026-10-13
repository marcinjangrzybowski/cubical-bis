module Cubical.Analysis.Complex.FundamentalTheorem.Descent.StableTriple where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.FinData as Fin using (Fin)
open import Cubical.Data.Sigma
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.FiniteIndices
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.NearMaximumStep
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.NearMaximumChain
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Radii

module StableNearMaxima {n} (coefficients : Fin (suc n) → ℝ) (q : ℝ) (ε : ℚ₊) where
  open FiniteNearMaxima coefficients q ε

  ThreeNearMaxima : ℝ → Fin (suc n) → Type₀
  ThreeNearMaxima r k = PowerNearMaximum coefficients r ε k ×
    PowerNearMaximum coefficients (q · r) ε k ×
    PowerNearMaximum coefficients (q · (q · r)) ε k

  StableTriple : ℕ → ℝ → Type₀
  StableTriple steps r = Σ[ offset ∈ ℕ ] (suc (suc offset) ℕ.≤ steps) ×
    (Σ[ k ∈ Fin (suc n) ] ThreeNearMaxima (shrinkRadius q offset r) k)

  extractStableTriple : ∀ steps r k (chain : NearMaximumChain steps r k) →
    EqualIndexTriple (chainIndices steps r k chain) → StableTriple steps r
  extractStableTriple zero r k chain (later ())
  extractStableTriple (suc (suc steps)) r k
      (maximum , j , decreases , next , l , decreases′ , tail) (here first second) =
    zero , ℕ.suc-≤-suc (ℕ.suc-≤-suc ℕ.zero-≤) , k , maximum ,
      subst (PowerNearMaximum coefficients (q · r) ε) (sym (Fin.inj-toℕ first)) next ,
      subst (PowerNearMaximum coefficients (q · (q · r)) ε)
        (sym (Fin.inj-toℕ (first ∙ second))) (chainHead steps (q · (q · r)) l tail)
    where
    chainHead : ∀ steps r k → NearMaximumChain steps r k → PowerNearMaximum coefficients r ε k
    chainHead zero r k maximum = maximum
    chainHead (suc steps) r k (maximum , tail) = maximum
  extractStableTriple (suc steps) r k (maximum , j , decreases , tail) (later triple) =
    let offset , bounded , l , stable = extractStableTriple steps (q · r) j tail triple
    in suc offset , ℕ.suc-≤-suc bounded , l , stable
