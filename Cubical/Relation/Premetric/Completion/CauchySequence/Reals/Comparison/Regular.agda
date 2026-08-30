module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Relation.Premetric.Instances.Rationals using
  (ℚPremetricSpace)

open import Cubical.HITs.CauchyRealsP.Foundation.Closeness as CR

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real

import Cubical.Relation.Premetric.Completion.CauchySequence.Comparison.Regular
  as RegularComparison

module C = RegularComparison ℚPremetricSpace


-- The regular completion maps canonically into the Cauchy-sequence
-- completion because the latter is complete in the ordinary premetric sense.

fromRegularⁿ :
  NE[ CR.ℝPremetricSpace , Real.ℝPremetricSpace ]
fromRegularⁿ = C.fromRegularⁿ

fromRegular : CR.ℝ → Real.ℝ
fromRegular = fst fromRegularⁿ

fromRegular-rat : ∀ q →
  fromRegular (CR.rat q) ≡ Real.ιℚ q
fromRegular-rat q =
  funExt⁻ C.fromRegular-ι q

fromRegular-pres≈ : ∀ {x y ε} →
  x CR.∼[ ε ] y →
  fromRegular x Real.Base.≈ᶜ[ ε ]
    fromRegular y
fromRegular-pres≈ {x} {y} {ε} x∼y =
  fromRegularⁿ .snd .IsNonExpanding.pres≈ x y ε x∼y
