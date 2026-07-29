module Cubical.Categories.Instances.PremetricSpaces where

-- The current premetric mapping theory constructs these categories together
-- with the mapping classes.  Keep that implementation as the source of truth
-- while providing the shorter names of the dedicated category module.
open import Cubical.Relation.Premetric.Mappings
  public using (isUnivalentPrSpacesⁿ)

open Cubical.Relation.Premetric.Mappings.CategoryStructures
  public
  renaming
    ( PremetricSpaceCategoryᶜ  to PrSpacesᶜ
    ; PremetricSpaceCategoryᵘᶜ to PrSpacesᵘᶜ
    ; PremetricSpaceCategoryᴸ  to PrSpacesᴸ
    ; PremetricSpaceCategoryⁿ  to PrSpacesⁿ
    )
