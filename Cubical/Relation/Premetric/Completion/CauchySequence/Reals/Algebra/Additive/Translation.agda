module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Translation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚO
open import Cubical.Data.Rationals.Order.AbsoluteValue

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open OrderedCommRingTheory ℚOrderedCommRing

open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Relation.Premetric.Instances.Rationals using
  (ℚPremetricSpace)

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real

import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.NonExpanding
  as NonExpandingDefinition

private
  module L = NonExpandingDefinition ℚPremetricSpace ℚPremetricSpace


rationalTranslationⁿ : ℚ → NE[ ℚPremetricSpace , ℚPremetricSpace ]
rationalTranslationⁿ c .fst q = q ℚR.+ c
rationalTranslationⁿ c .snd .IsNonExpanding.pres≈ q r ε q≈r =
  subst (ℚO._< fst ε)
    (cong
      {x = q ℚR.- r}
      {y = (q ℚR.+ c) ℚR.- (r ℚR.+ c)}
      abs ℚ!)
    q≈r

translationⁿ : ℚ →
  NE[ Real.ℝPremetricSpace , Real.ℝPremetricSpace ]
translationⁿ c = L.liftNonExpanding (rationalTranslationⁿ c)

translate : ℚ → Real.ℝ → Real.ℝ
translate c = fst (translationⁿ c)

translate-ι : ∀ c q →
  translate c (Real.ιℚ q) ≡ Real.ιℚ (q ℚR.+ c)
translate-ι c q = refl

translate-lim : ∀ c x gx →
  translate c (Real.Base.lim x gx) ≡
  Real.Base.lim (translate c ∘ x)
    (L.WithNonExpanding.mapWitness
      (fst (rationalTranslationⁿ c))
      (snd (rationalTranslationⁿ c)) gx)
translate-lim c x gx = refl

translate-pres≈ : ∀ c x y ε →
  x Real.Base.≈ᶜ[ ε ] y →
  translate c x Real.Base.≈ᶜ[ ε ] translate c y
translate-pres≈ c x y ε =
  translationⁿ c .snd .IsNonExpanding.pres≈ x y ε


translation-zeroⁿ : translationⁿ 0 ≡ idⁿ
translation-zeroⁿ =
  L.nonExpandingExtensionality
    (translationⁿ 0) idⁿ
    (funExt λ q → cong Real.ιℚ ℚ!)

translate-zero : ∀ x → translate 0 x ≡ x
translate-zero x = funExt⁻ (cong fst translation-zeroⁿ) x

translation-addⁿ : ∀ c d →
  translationⁿ c ∘NE translationⁿ d ≡
    translationⁿ (d ℚR.+ c)
translation-addⁿ c d =
  L.nonExpandingExtensionality
    (translationⁿ c ∘NE translationⁿ d)
    (translationⁿ (d ℚR.+ c))
    (funExt λ q → cong Real.ιℚ ℚ!)

translate-add : ∀ c d x →
  translate c (translate d x) ≡ translate (d ℚR.+ c) x
translate-add c d x =
  funExt⁻ (cong fst (translation-addⁿ c d)) x

translate-inverse : ∀ c x →
  translate (ℚR.- c) (translate c x) ≡ x
translate-inverse c x =
  translate-add (ℚR.- c) c x
  ∙ cong (λ d → translate d x) ℚ!
  ∙ translate-zero x
