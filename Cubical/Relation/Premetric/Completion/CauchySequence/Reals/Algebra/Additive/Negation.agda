module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation where

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


rationalNegationⁿ : NE[ ℚPremetricSpace , ℚPremetricSpace ]
rationalNegationⁿ .fst q = ℚR.- q
rationalNegationⁿ .snd .IsNonExpanding.pres≈ q r ε q≈r =
  subst (ℚO._< fst ε)
    (abs-Comm q r
      ∙ cong
          {x = r ℚR.- q}
          {y = (ℚR.- q) ℚR.- (ℚR.- r)}
          abs ℚ!)
    q≈r


negationⁿ : NE[ Real.ℝPremetricSpace , Real.ℝPremetricSpace ]
negationⁿ = L.liftNonExpanding rationalNegationⁿ

infix 8 -_

-_ : Real.ℝ → Real.ℝ
-_ = fst negationⁿ

neg-seqWitness : ∀ {x} → Real.Base.IsCauchySequence x →
  Real.Base.IsCauchySequence (-_ ∘ x)
neg-seqWitness =
  L.WithNonExpanding.mapWitness
    (fst rationalNegationⁿ) (snd rationalNegationⁿ)

neg-ι : ∀ q → - Real.ιℚ q ≡ Real.ιℚ (ℚR.- q)
neg-ι q = refl

neg-lim : ∀ x gx →
  - Real.Base.lim x gx ≡
  Real.Base.lim (-_ ∘ x)
    (neg-seqWitness gx)
neg-lim x gx = refl

neg-pres≈ : ∀ x y ε →
  x Real.Base.≈ᶜ[ ε ] y →
  (- x) Real.Base.≈ᶜ[ ε ] (- y)
neg-pres≈ x y ε =
  negationⁿ .snd .IsNonExpanding.pres≈ x y ε


negation-involutiveⁿ :
  negationⁿ ∘NE negationⁿ ≡ idⁿ
negation-involutiveⁿ =
  L.nonExpandingExtensionality
    (negationⁿ ∘NE negationⁿ) idⁿ
    (funExt λ q → cong Real.ιℚ ℚ!)

neg-involutive : ∀ x → - (- x) ≡ x
neg-involutive x =
  funExt⁻ (cong fst negation-involutiveⁿ) x
