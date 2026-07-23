module Cubical.HITs.CauchyReals.Complex.Metric.Coordinates.Projections.Imaginary where

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
  im-difference-close : ∀ z w ε → z ≈ℂ[ ε ] w →
    absᵣ (im z -ᵣ im w) <ᵣ rat (fst ε)
  im-difference-close z w ε z≈w =
    isTrans≤<ᵣ _ _ _ (abs-im-difference≤modulus z w) z≈w


opaque
  im-pres∼ : ∀ z w ε → z ≈ℂ[ ε ] w → im z ∼[ ε ] im w
  im-pres∼ z w ε z≈w =
    invEq (∼≃abs<ε (im z) (im w) ε)
      (im-difference-close z w ε z≈w)


opaque
  im-pres≈ : ∀ z w ε → z ≈ℂ[ ε ] w → im z ≈ℝ[ ε ] im w
  im-pres≈ z w ε z≈w =
    ∼→≈ℝ (im z) (im w) ε (im-pres∼ z w ε z≈w)


imIsNonExpanding :
  IsNonExpanding (snd ℂPremetricSpace) im (snd ℝPremetricSpace)
IsNonExpanding.pres≈ imIsNonExpanding = im-pres≈


imℂNE : NE[ ℂPremetricSpace , ℝPremetricSpace ]
imℂNE = im , imIsNonExpanding
