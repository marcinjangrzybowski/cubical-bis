module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚO
open import Cubical.Data.Rationals.Order.AbsoluteValue

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Relation.Premetric.Instances.Rationals using
  (ℚPremetricSpace)

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg

import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.NonExpanding
  as NonExpandingDefinition

private
  module L = NonExpandingDefinition ℚPremetricSpace ℚPremetricSpace
  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing


rationalAbsoluteValueⁿ : NE[ ℚPremetricSpace , ℚPremetricSpace ]
rationalAbsoluteValueⁿ .fst = ℚOrder.abs
rationalAbsoluteValueⁿ .snd .IsNonExpanding.pres≈ x y ε x∼y =
  ℚO.isTrans≤< _ _ _
    (absFrom≤×≤
      (ℚOrder.abs (x ℚR.- y))
      (ℚOrder.abs x ℚR.- ℚOrder.abs y)
      (subst2 ℚO._≤_
        (cong ℚR.-_ (sym (ℚOrder.abs-Comm x y)))
        ℚ!
        (ℚO.minus-≤
          (ℚOrder.abs y ℚR.- ℚOrder.abs x)
          (ℚOrder.abs (y ℚR.- x))
          (ℚOrder.abs-abs≤abs- y x)))
      (ℚOrder.abs-abs≤abs- x y))
    x∼y


absoluteValueⁿ :
  NE[ Real.ℝPremetricSpace , Real.ℝPremetricSpace ]
absoluteValueⁿ = L.liftNonExpanding rationalAbsoluteValueⁿ

absℝ : Real.ℝ → Real.ℝ
absℝ = fst absoluteValueⁿ

absℝ-seqWitness : ∀ {x} → Real.Base.IsCauchySequence x →
  Real.Base.IsCauchySequence (absℝ ∘ x)
absℝ-seqWitness =
  L.WithNonExpanding.mapWitness
    (fst rationalAbsoluteValueⁿ) (snd rationalAbsoluteValueⁿ)

absℝ-ι : ∀ q → absℝ (Real.ιℚ q) ≡ Real.ιℚ (ℚOrder.abs q)
absℝ-ι q = refl

absℝ-lim : ∀ x gx →
  absℝ (Real.Base.lim x gx) ≡
  Real.Base.lim (absℝ ∘ x)
    (absℝ-seqWitness gx)
absℝ-lim x gx = refl

absℝ-pres≈ : ∀ x y ε →
  x Real.Base.≈ᶜ[ ε ] y →
  absℝ x Real.Base.≈ᶜ[ ε ] absℝ y
absℝ-pres≈ x y ε =
  absoluteValueⁿ .snd .IsNonExpanding.pres≈ x y ε


absoluteValue-idempotentⁿ :
  absoluteValueⁿ ∘NE absoluteValueⁿ ≡ absoluteValueⁿ
absoluteValue-idempotentⁿ =
  L.nonExpandingExtensionality
    (absoluteValueⁿ ∘NE absoluteValueⁿ) absoluteValueⁿ
    (funExt λ q →
      cong Real.ιℚ
        (ℚOrder.0≤→abs≡id
          (ℚOrder.abs q) (ℚOrder.0≤abs q)))

absℝ-idempotent : ∀ x → absℝ (absℝ x) ≡ absℝ x
absℝ-idempotent x =
  funExt⁻ (cong fst absoluteValue-idempotentⁿ) x

absoluteValue-after-negationⁿ :
  absoluteValueⁿ ∘NE Neg.negationⁿ ≡ absoluteValueⁿ
absoluteValue-after-negationⁿ =
  L.nonExpandingExtensionality
    (absoluteValueⁿ ∘NE Neg.negationⁿ) absoluteValueⁿ
    (funExt λ q → cong Real.ιℚ (sym (-abs q)))

absℝ-neg : ∀ x → absℝ (Neg.- x) ≡ absℝ x
absℝ-neg x =
  funExt⁻ (cong fst absoluteValue-after-negationⁿ) x

absℝ-zero : absℝ (Real.ιℚ 0) ≡ Real.ιℚ 0
absℝ-zero =
  absℝ-ι 0
  ∙ cong Real.ιℚ (ℚOrder.abs0)
