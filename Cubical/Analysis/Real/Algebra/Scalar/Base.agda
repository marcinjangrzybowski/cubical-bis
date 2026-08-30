module Cubical.Analysis.Real.Algebra.Scalar.Base where

open import Cubical.Foundations.Prelude

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

open import Cubical.Analysis.Real.Base
import Cubical.Analysis.Completion.Lipschitz as LipschitzDefinition

private
  module L = LipschitzDefinition ℚPremetricSpace ℚPremetricSpace
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)

open PositiveRationals
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing


-- Multiplication by a fixed rational has a global quantitative bound.  The
-- lower bound of one makes the witness positive even when the scalar is zero.

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
  Σ[ F ∈ (ℝ → ℝ) ]
    IsLipschitzWith
      (ℝPremetricSpace .snd) F
      (ℝPremetricSpace .snd) (rationalScalarBound c)
scalarLipschitz c =
  L.liftLipschitzWith
    (rationalScalarBound c) (rationalScale c)
    (rationalScaleIsLipschitz c)

infixr 9 _⋆_

_⋆_ : ℚ → ℝ → ℝ
c ⋆ x = scalarLipschitz c .fst x

scalar-rat : ∀ c q →
  c ⋆ rat q ≡ rat (c ℚR.· q)
scalar-rat c q =
  L.liftLipschitzWith-ι
    (rationalScalarBound c) (rationalScale c)
    (rationalScaleIsLipschitz c) q

scalar-pres∼ : ∀ c x y ε →
  x ∼[ ε ] y →
  (c ⋆ x) ∼[ rationalScalarBound c ·₊ ε ] (c ⋆ y)
scalar-pres∼ c =
  scalarLipschitz c .snd .IsLipschitzWith.pres≈

scalar-isLipschitzWith : ∀ c →
  IsLipschitzWith
    (ℝPremetricSpace .snd) (c ⋆_)
    (ℝPremetricSpace .snd) (rationalScalarBound c)
scalar-isLipschitzWith c = scalarLipschitz c .snd

scalar-isLipschitz : ∀ c →
  isLipschitz
    (ℝPremetricSpace .snd) (c ⋆_)
    (ℝPremetricSpace .snd)
scalar-isLipschitz c =
  ∣ rationalScalarBound c , scalar-isLipschitzWith c ∣₁

scalar-isUniformlyContinuous : ∀ c →
  isUniformlyContinuous
    (ℝPremetricSpace .snd) (c ⋆_)
    (ℝPremetricSpace .snd)
scalar-isUniformlyContinuous c =
  isLipschitz→isUniformlyContinuous
    (ℝPremetricSpace .snd) (c ⋆_)
    (ℝPremetricSpace .snd)
    (scalar-isLipschitz c)

scalar-isContinuous : ∀ c →
  isContinuous
    (ℝPremetricSpace .snd) (c ⋆_)
    (ℝPremetricSpace .snd)
scalar-isContinuous c =
  isLipschitz→isContinuous
    (ℝPremetricSpace .snd) (c ⋆_)
    (ℝPremetricSpace .snd)
    (scalar-isLipschitz c)
