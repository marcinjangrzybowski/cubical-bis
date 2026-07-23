module Cubical.HITs.CauchyReals.Complex.Metric.Mappings where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Mappings

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Conjugation
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Metric.Base

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


opaque
  translate-difference-path : ∀ z w u →
    (z +ℂ u) -ℂ (w +ℂ u) ≡ z -ℂ w
  translate-difference-path _ _ _ = ℂ≡ ℝ! ℝ!


opaque
  translateℂ-pres≈ : ∀ u z w ε → z ≈ℂ[ ε ] w →
    (z +ℂ u) ≈ℂ[ ε ] (w +ℂ u)
  translateℂ-pres≈ u z w ε =
    subst (_<ᵣ rat (fst ε))
      (sym (cong modulus (translate-difference-path z w u)))


translateℂIsNonExpanding : ∀ u →
  IsNonExpanding (snd ℂPremetricSpace) (_+ℂ u) (snd ℂPremetricSpace)
IsNonExpanding.pres≈ (translateℂIsNonExpanding u) = translateℂ-pres≈ u


translateℂNE : ℂ → NE[ ℂPremetricSpace , ℂPremetricSpace ]
translateℂNE u = (_+ℂ u) , translateℂIsNonExpanding u


opaque
  neg-difference-path : ∀ z w →
    (-ℂ z) -ℂ (-ℂ w) ≡ -ℂ (z -ℂ w)
  neg-difference-path _ _ = ℂ≡ ℝ! ℝ!


opaque
  negℂ-pres≈ : ∀ z w ε → z ≈ℂ[ ε ] w → (-ℂ z) ≈ℂ[ ε ] (-ℂ w)
  negℂ-pres≈ z w ε = subst (_<ᵣ rat (fst ε))
    (sym (cong modulus (neg-difference-path z w) ∙ modulus-neg (z -ℂ w)))


negℂIsNonExpanding :
  IsNonExpanding (snd ℂPremetricSpace) -ℂ_ (snd ℂPremetricSpace)
IsNonExpanding.pres≈ negℂIsNonExpanding = negℂ-pres≈


negℂNE : NE[ ℂPremetricSpace , ℂPremetricSpace ]
negℂNE = -ℂ_ , negℂIsNonExpanding


opaque
  conj-difference-path : ∀ z w →
    conj z -ℂ conj w ≡ conj (z -ℂ w)
  conj-difference-path _ _ = ℂ≡ ℝ! ℝ!


opaque
  conj-pres≈ : ∀ z w ε → z ≈ℂ[ ε ] w → conj z ≈ℂ[ ε ] conj w
  conj-pres≈ z w ε = subst (_<ᵣ rat (fst ε))
    (sym (cong modulus (conj-difference-path z w) ∙ modulus-conj (z -ℂ w)))


conjIsNonExpanding :
  IsNonExpanding (snd ℂPremetricSpace) conj (snd ℂPremetricSpace)
IsNonExpanding.pres≈ conjIsNonExpanding = conj-pres≈


conjNE : NE[ ℂPremetricSpace , ℂPremetricSpace ]
conjNE = conj , conjIsNonExpanding
