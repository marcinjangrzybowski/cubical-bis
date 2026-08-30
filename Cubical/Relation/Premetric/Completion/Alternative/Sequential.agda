open import Cubical.Relation.Premetric.Base

-- The sequence-backed presentation of completion.  Its limit constructor
-- takes an ordinary natural-number sequence and only a propositionally
-- truncated Cauchy witness.  Base contains the HIT and eliminators;
-- Properties installs the derived premetric structure and density lemmas.

module Cubical.Relation.Premetric.Completion.Alternative.Sequential
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  M' public
open import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  M' public
