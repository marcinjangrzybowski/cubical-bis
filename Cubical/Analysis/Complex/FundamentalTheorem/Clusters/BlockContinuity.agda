module Cubical.Analysis.Complex.FundamentalTheorem.Clusters.BlockContinuity where

-- A whole rational modulus controls both block factors. This is the finite
-- estimate needed for lifting a stable split to completed configurations;
-- it does not assume that such a split has already been constructed there.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Vec using (Vec; _++_)
open import Cubical.Data.Sigma
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.FactorContinuity
import Cubical.Analysis.Complex.FundamentalTheorem.Completion.FiniteMatching as Finite
open import Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Geometry
open import Cubical.Analysis.Complex.FundamentalTheorem.Clusters.BlockMatching

private module M = Finite ℂPremetricSpace

blockFactorModulus : ℕ → ℕ → ℚ₊ → ℚ₊ → ℚ₊ → ℚ₊
blockFactorModulus m n bound gap ε = min₊ (gap /2₊)
  (min₊ (factorContinuityModulus m bound ε) (factorContinuityModulus n bound ε))

blockFactor-continuity : ∀ {m n} (xs xs′ : Vec ℂ m) (ys ys′ : Vec ℂ n) bound gap ε →
  RootsBounded xs bound → RootsBounded xs′ bound → RootsBounded ys bound → RootsBounded ys′ bound →
  ConfigurationGap xs ys′ gap → ConfigurationGap ys xs′ gap →
  MatchingClose (xs ++ ys) (blockFactorModulus m n bound gap ε) (xs′ ++ ys′) →
  CoefficientCloseness (linearFactors xs) ε (linearFactors xs′) ×
    CoefficientCloseness (linearFactors ys) ε (linearFactors ys′)
blockFactor-continuity {m} {n} xs xs′ ys ys′ bound gap ε xb xb′ yb yb′ first second matched =
  factorContinuityEstimate m bound ε xs xs′ xb xb′
    (M.match-monotone xs xs′ (min₊ μ ν) μ (min₊≤L μ ν)
      (M.match-monotone xs xs′ δ (min₊ μ ν) (min₊≤R (gap /2₊) (min₊ μ ν)) (fst blocks))) ,
  factorContinuityEstimate n bound ε ys ys′ yb yb′
    (M.match-monotone ys ys′ (min₊ μ ν) ν (min₊≤R μ ν)
      (M.match-monotone ys ys′ δ (min₊ μ ν) (min₊≤R (gap /2₊) (min₊ μ ν)) (snd blocks)))
  where
  μ ν δ : ℚ₊
  μ = factorContinuityModulus m bound ε
  ν = factorContinuityModulus n bound ε
  δ = blockFactorModulus m n bound gap ε

  blocks : MatchingClose xs δ xs′ × MatchingClose ys δ ys′
  blocks = matching-separated-blocks-at xs xs′ ys ys′ gap δ
    (min₊≤L (gap /2₊) (min₊ μ ν)) first second matched
