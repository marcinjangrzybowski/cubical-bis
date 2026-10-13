module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Identities.Squares where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Algebra.Scalar.Laws
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pythagorean
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Identities
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry

private
  module R = RingProperties.RingTheory (CommRing→Ring ℝCommRing)

  opaque
    powTwo : ∀ x → powℝ x 2 ≡ x · x
    powTwo x = cong (x ·_) (mulIdR x)

    twice : ∀ x → realNatural 2 · x ≡ x + x
    twice x = cong (_· x) (realNatural-suc 1)
      ∙ mulDistL 1ℝ 1ℝ x ∙ cong₂ _+_ (mulIdL x) (mulIdL x)

    complementTwice : ∀ a b → a - (a - b) ≡ b
    complementTwice a b = cong (a +_) (negSub a b)
      ∙ addComm a (b - a) ∙ subAddCancel b a

    restoreFromDifference : ∀ a b → a + (b - a) ≡ b
    restoreFromDifference a b = addComm a (b - a) ∙ subAddCancel b a

    doubleHalf : ∀ x → (quarterTurnHalf ⋆ x) + (quarterTurnHalf ⋆ x) ≡ x
    doubleHalf x = sym (scalar-dist-right quarterTurnHalf x x)
      ∙ quarterTurnHalfScalar-double x

opaque
  cosℝ-square-complement : ∀ x → cosℝ x · cosℝ x ≡ 1ℝ - sinℝ x · sinℝ x
  cosℝ-square-complement x = sym (R.plusMinus (cosℝ x · cosℝ x) (sinℝ x · sinℝ x))
    ∙ cong (_- sinℝ x · sinℝ x)
        (addComm (cosℝ x · cosℝ x) (sinℝ x · sinℝ x) ∙ sin²+cos²≡1 x)

  sinℝ-square-complement : ∀ x → sinℝ x · sinℝ x ≡ 1ℝ - cosℝ x · cosℝ x
  sinℝ-square-complement x = sym (R.plusMinus (sinℝ x · sinℝ x) (cosℝ x · cosℝ x))
    ∙ cong (_- cosℝ x · cosℝ x) (sin²+cos²≡1 x)

  sinℝ-pow²+cosℝ-pow²≡1 : ∀ x → powℝ (sinℝ x) 2 + powℝ (cosℝ x) 2 ≡ 1ℝ
  sinℝ-pow²+cosℝ-pow²≡1 x = cong₂ _+_ (powTwo (sinℝ x)) (powTwo (cosℝ x))
    ∙ sin²+cos²≡1 x

  sinℝ-two-mul : ∀ x → sinℝ (realNatural 2 · x) ≡ realNatural 2 · (sinℝ x · cosℝ x)
  sinℝ-two-mul x = cong sinℝ (twice x) ∙ sinℝ-double x ∙ sym (twice (sinℝ x · cosℝ x))

  cosℝ-two-mul : ∀ x → cosℝ (realNatural 2 · x) ≡ powℝ (cosℝ x) 2 - powℝ (sinℝ x) 2
  cosℝ-two-mul x = cong cosℝ (twice x) ∙ cosℝ-double x
    ∙ cong₂ _-_ (sym (powTwo (cosℝ x))) (sym (powTwo (sinℝ x)))

  cosℝ-two-mul-sinSquare : ∀ x →
    cosℝ (realNatural 2 · x) ≡ 1ℝ - realNatural 2 · powℝ (sinℝ x) 2
  cosℝ-two-mul-sinSquare x = cong cosℝ (twice x) ∙ cosℝ-double≡one-sub-doubleSinSquare x
    ∙ cong (λ z → 1ℝ - z) (sym (twice (sinℝ x · sinℝ x))
      ∙ cong (realNatural 2 ·_) (sym (powTwo (sinℝ x))))

  cosℝ-two-mul-cosSquare : ∀ x →
    cosℝ (realNatural 2 · x) ≡ realNatural 2 · powℝ (cosℝ x) 2 - 1ℝ
  cosℝ-two-mul-cosSquare x = cong cosℝ (twice x) ∙ cosℝ-double≡doubleCosSquare-sub-one x
    ∙ cong (_- 1ℝ) (sym (twice (cosℝ x · cosℝ x))
      ∙ cong (realNatural 2 ·_) (sym (powTwo (cosℝ x))))

  sinℝ-square-reduction : ∀ x → sinℝ x · sinℝ x ≡
    quarterTurnHalf ⋆ (1ℝ - cosℝ (x + x))
  sinℝ-square-reduction x = sym (quarterTurnHalfScalar-double (sinℝ x · sinℝ x))
    ∙ cong (quarterTurnHalf ⋆_)
      (sym (complementTwice 1ℝ ((sinℝ x · sinℝ x) + (sinℝ x · sinℝ x)))
      ∙ cong (λ z → 1ℝ - z) (sym (cosℝ-double≡one-sub-doubleSinSquare x)))

  cosℝ-square-reduction : ∀ x → cosℝ x · cosℝ x ≡
    quarterTurnHalf ⋆ (1ℝ + cosℝ (x + x))
  cosℝ-square-reduction x = sym (quarterTurnHalfScalar-double (cosℝ x · cosℝ x))
    ∙ cong (quarterTurnHalf ⋆_)
      (sym (restoreFromDifference 1ℝ ((cosℝ x · cosℝ x) + (cosℝ x · cosℝ x)))
      ∙ cong (1ℝ +_) (sym (cosℝ-double≡doubleCosSquare-sub-one x)))

  sinℝ-half-square : ∀ x →
    sinℝ (quarterTurnHalf ⋆ x) · sinℝ (quarterTurnHalf ⋆ x) ≡
    quarterTurnHalf ⋆ (1ℝ - cosℝ x)
  sinℝ-half-square x = sinℝ-square-reduction (quarterTurnHalf ⋆ x)
    ∙ cong (λ z → quarterTurnHalf ⋆ (1ℝ - cosℝ z)) (doubleHalf x)

  cosℝ-half-square : ∀ x →
    cosℝ (quarterTurnHalf ⋆ x) · cosℝ (quarterTurnHalf ⋆ x) ≡
    quarterTurnHalf ⋆ (1ℝ + cosℝ x)
  cosℝ-half-square x = cosℝ-square-reduction (quarterTurnHalf ⋆ x)
    ∙ cong (λ z → quarterTurnHalf ⋆ (1ℝ + cosℝ z)) (doubleHalf x)
