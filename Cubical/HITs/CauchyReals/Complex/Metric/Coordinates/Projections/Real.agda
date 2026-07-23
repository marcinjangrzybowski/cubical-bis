module Cubical.HITs.CauchyReals.Complex.Metric.Coordinates.Projections.Real where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Premetric.Mappings

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Metric.Base
open import Cubical.HITs.CauchyReals.Complex.Metric.Coordinates.LowerBounds


opaque
  re-difference-close : ∀ z w ε → z ≈ℂ[ ε ] w →
    absᵣ (re z -ᵣ re w) <ᵣ rat (fst ε)
  re-difference-close z w ε z≈w =
    isTrans≤<ᵣ _ _ _ (abs-re-difference≤modulus z w) z≈w


opaque
  re-pres∼ : ∀ z w ε → z ≈ℂ[ ε ] w → re z ∼[ ε ] re w
  re-pres∼ z w ε z≈w =
    invEq (∼≃abs<ε (re z) (re w) ε)
      (re-difference-close z w ε z≈w)


opaque
  re-pres≈ : ∀ z w ε → z ≈ℂ[ ε ] w → re z ≈ℝ[ ε ] re w
  re-pres≈ z w ε z≈w =
    ∼→≈ℝ (re z) (re w) ε (re-pres∼ z w ε z≈w)


reIsNonExpanding :
  IsNonExpanding (snd ℂPremetricSpace) re (snd ℝPremetricSpace)
IsNonExpanding.pres≈ reIsNonExpanding = re-pres≈


reℂNE : NE[ ℂPremetricSpace , ℝPremetricSpace ]
reℂNE = re , reIsNonExpanding
