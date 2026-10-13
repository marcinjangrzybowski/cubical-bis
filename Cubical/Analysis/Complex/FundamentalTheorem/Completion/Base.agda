module Cubical.Analysis.Complex.FundamentalTheorem.Completion.Base where

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Completion
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Gaussian
import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Construction as Construction

module Roots (n : ℕ) = Construction gaussianSpace n

-- The completion object is constructed output. Insertion, its exact
-- matching isometry, density, regular completeness, and sequential
-- completeness are all supplied by this value.
rootMultisetCompletion : (n : ℕ) → RootMultisetCompletion n
rootMultisetCompletion n = Roots.finiteMatchingCompletion n
