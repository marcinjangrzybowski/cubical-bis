module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals using
  (ℚPremetricSpace)

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.Lipschitz
  as LipschitzDefinition

private
  module L = LipschitzDefinition ℚPremetricSpace ℚPremetricSpace
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)

open PositiveRationals
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing


-- Multiplication by a fixed rational has a global bound.  This is the
-- constructive fragment of multiplication which does not need bounds on a
-- varying real argument.

rationalScalarBound : ℚ → ℚ₊
rationalScalarBound c = ℚ.maxWithPos 1 (abs c)

rationalScale : ℚ → ℚ → ℚ
rationalScale c q = c ℚR.· q

rationalScaleIsLipschitz : ∀ c →
  IsLipschitzWith
    (ℚPremetricSpace .snd) (rationalScale c)
    (ℚPremetricSpace .snd) (rationalScalarBound c)
rationalScaleIsLipschitz c
  .IsLipschitzWith.pres≈ q r ε q≈r = begin<
  abs ((c ℚR.· q) ℚR.- (c ℚR.· r))
    ≡→≤⟨ cong abs (sym (ℚRing.·DistR- c q r))
          ∙ sym (abs·abs c (q ℚR.- r)) ⟩
  abs c ℚR.· abs (q ℚR.- r)
    ≤⟨ ·MonoR≤ (abs c) (fst (rationalScalarBound c))
        (abs (q ℚR.- r)) (0≤abs (q ℚR.- r))
        (ℚ.≤max' 1 (abs c)) ⟩
  fst (rationalScalarBound c) ℚR.· abs (q ℚR.- r)
    <⟨ ·MonoL< (abs (q ℚR.- r)) (fst ε)
        (fst (rationalScalarBound c))
        (snd (rationalScalarBound c)) q≈r ⟩
  fst (rationalScalarBound c ·₊ ε) ◾


scalarLipschitz : ∀ c →
  Σ[ F ∈ (Real.ℝ → Real.ℝ) ]
    IsLipschitzWith
      (Real.ℝPremetricSpace .snd) F
      (Real.ℝPremetricSpace .snd) (rationalScalarBound c)
scalarLipschitz c =
  L.liftLipschitzWith
    (rationalScalarBound c) (rationalScale c)
    (rationalScaleIsLipschitz c)

infixr 9 _⋆_

_⋆_ : ℚ → Real.ℝ → Real.ℝ
c ⋆ x = scalarLipschitz c .fst x

scalar-seqWitness : ∀ c {x} → Real.Base.IsCauchySequence x →
  Real.Base.IsCauchySequence ((_⋆_ c) ∘ x)
scalar-seqWitness c =
  L.WithLipschitz.mapWitness
    (rationalScalarBound c) (rationalScale c)
    (rationalScaleIsLipschitz c)

scalar-ι : ∀ c q →
  c ⋆ Real.ιℚ q ≡ Real.ιℚ (c ℚR.· q)
scalar-ι c q = refl

scalar-lim : ∀ c x gx →
  c ⋆ Real.Base.lim x gx ≡
  Real.Base.lim ((_⋆_ c) ∘ x)
    (scalar-seqWitness c gx)
scalar-lim c x gx = refl

scalar-pres≈ : ∀ c x y ε →
  x Real.Base.≈ᶜ[ ε ] y →
  (c ⋆ x) Real.Base.≈ᶜ[ rationalScalarBound c ·₊ ε ] (c ⋆ y)
scalar-pres≈ c = scalarLipschitz c .snd .IsLipschitzWith.pres≈

scalar-isLipschitz : ∀ c →
  isLipschitz
    (Real.ℝPremetricSpace .snd) (_⋆_ c)
    (Real.ℝPremetricSpace .snd)
scalar-isLipschitz c =
  ∣ rationalScalarBound c , scalarLipschitz c .snd ∣₁

scalar-isUniformlyContinuous : ∀ c →
  isUniformlyContinuous
    (Real.ℝPremetricSpace .snd) (_⋆_ c)
    (Real.ℝPremetricSpace .snd)
scalar-isUniformlyContinuous c =
  isLipschitz→isUniformlyContinuous
    (Real.ℝPremetricSpace .snd) (_⋆_ c)
    (Real.ℝPremetricSpace .snd)
    (scalar-isLipschitz c)

scalar-isContinuous : ∀ c →
  isContinuous
    (Real.ℝPremetricSpace .snd) (_⋆_ c)
    (Real.ℝPremetricSpace .snd)
scalar-isContinuous c =
  isLipschitz→isContinuous
    (Real.ℝPremetricSpace .snd) (_⋆_ c)
    (Real.ℝPremetricSpace .snd)
    (scalar-isLipschitz c)
