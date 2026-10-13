module Cubical.Analysis.Complex.FundamentalTheorem.Completion where

open import Cubical.Foundations.Prelude using (_,_)
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Completion
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Base public using (rootMultisetCompletion)
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Density public
  using (gaussianFactors; gaussian-factors-approximate; gaussian-factor-density)
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Extension public
  using (completedFactors; completedFactors-insert)
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.FactorMap public
  using (completedFactors-injective; completedFactors-continuity;
    completedFactors-inverse-continuity; completedFactors-dense)
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Correspondence public
  using (completedRoots; factors-roots; roots-factors;
    completedFactorEquivalence; rootMultisetCorrespondence)

-- The original surveyed statement, including a constructed completion,
-- an equivalence, the finite-factor law, and both whole local moduli.
completedMultisetFundamentalTheorem : CompletedMultisetFundamentalTheorem
completedMultisetFundamentalTheorem n = rootMultisetCompletion n , rootMultisetCorrespondence n
