module Cubical.HITs.CauchyRealsP.Foundation.Approximation where

open import Cubical.HITs.CauchyRealsP.Foundation.Closeness public
open import Cubical.HITs.CauchyRealsP.Foundation.Rationals

open import
  Cubical.Relation.Premetric.Completion.Properties.Approximations

-- Every real is arbitrarily close to an embedded rational.  `showRational`
-- forgets the closeness witness and retains the truncated rational value.
open Show ℚPremetricSpace public
  renaming
    ( ∃approx to ∃ratApprox
    ; show    to showRational
    )
