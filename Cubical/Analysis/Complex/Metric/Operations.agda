module Cubical.Analysis.Complex.Metric.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric

refl∼ℂ : ∀ z ε → z ∼ℂ[ ε ] z
refl∼ℂ z ε = refl∼ (re z) ε , refl∼ (im z) ε

sym∼ℂ : ∀ z w ε → z ∼ℂ[ ε ] w → w ∼ℂ[ ε ] z
sym∼ℂ z w ε (r , i) = sym∼ (re z) (re w) ε r , sym∼ (im z) (im w) ε i

negℂ-presCloseness : ∀ z w ε → z ∼ℂ[ ε ] w → (-ℂ z) ∼ℂ[ ε ] (-ℂ w)
negℂ-presCloseness z w ε (r , i) =
  IsNonExpanding.pres≈ neg-isNonExpanding (re z) (re w) ε r ,
  IsNonExpanding.pres≈ neg-isNonExpanding (im z) (im w) ε i

addℂ-presClosenessL : ∀ c z w ε → z ∼ℂ[ ε ] w → (c +ℂ z) ∼ℂ[ ε ] (c +ℂ w)
addℂ-presClosenessL c z w ε (r , i) =
  add-pres∼₂ (re c) (re z) (re w) ε r , add-pres∼₂ (im c) (im z) (im w) ε i

addℂ-presClosenessR : ∀ c z w ε → z ∼ℂ[ ε ] w → (z +ℂ c) ∼ℂ[ ε ] (w +ℂ c)
addℂ-presClosenessR c z w ε (r , i) =
  add-pres∼₁ (re z) (re w) (re c) ε r , add-pres∼₁ (im z) (im w) (im c) ε i

addℂ-presHalfCloseness : ∀ a b c d ε →
  a ∼ℂ[ ε /2₊ ] b → c ∼ℂ[ ε /2₊ ] d → (a +ℂ c) ∼ℂ[ ε ] (b +ℂ d)
addℂ-presHalfCloseness a b c d ε (ar , ai) (cr , ci) =
  PremetricStr.subst≈ (ℝPremetricSpace .snd) _ _ (1/2∈ℚ./2+/2≡id (fst ε))
    (add-pres∼ (re a) (re b) (re c) (re d) (ε /2₊) (ε /2₊) ar cr) ,
  PremetricStr.subst≈ (ℝPremetricSpace .snd) _ _ (1/2∈ℚ./2+/2≡id (fst ε))
    (add-pres∼ (im a) (im b) (im c) (im d) (ε /2₊) (ε /2₊) ai ci)

subtractℂ-presClosenessL : ∀ c z w ε → z ∼ℂ[ ε ] w → (c -ℂ z) ∼ℂ[ ε ] (c -ℂ w)
subtractℂ-presClosenessL c z w ε close =
  addℂ-presClosenessL c (-ℂ z) (-ℂ w) ε (negℂ-presCloseness z w ε close)
