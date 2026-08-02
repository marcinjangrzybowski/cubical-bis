module Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.CauchyContinuousRationals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ

open import Cubical.Relation.Premetric.Instances.Rationals

open import Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.CauchyContinuous
  ℚPremetricSpace public


MapsRationalCauchySequences : (ℚ → S.ℭ̂ₛ) → Type₀
MapsRationalCauchySequences = MapsBaseCauchySequences

isCauchyContinuous→mapsRationalCauchySequences :
  ∀ {f} → IsCauchyContinuous f → MapsRationalCauchySequences f
isCauchyContinuous→mapsRationalCauchySequences =
  isCauchyContinuous→mapsBaseCauchySequences
