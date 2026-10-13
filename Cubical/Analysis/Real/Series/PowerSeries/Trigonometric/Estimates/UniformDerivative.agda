module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.UniformDerivative where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad using (_>>=_; return)
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.Relation.Premetric.Base

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.SharpBounds
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.AdditionDerived

private
  module R = RingProperties.RingTheory (CommRing→Ring ℝCommRing)
  module M = PremetricStr (snd ℝPremetricSpace)

  opaque
    swapLast : ∀ a b c → (a + b) + c ≡ (a + c) + b
    swapLast a b c = sym (addAssoc a b c)
      ∙ cong (a +_) (addComm b c) ∙ addAssoc a c b

    sineErrorAlgebra : ∀ s c h u v →
      (s · u + c · v) - u · h ≡ (s - h) · u + c · v
    sineErrorAlgebra s c h u v =
      cong (λ z → (s · u + c · v) - z) (mulComm u h)
      ∙ swapLast (s · u) (c · v) (- (h · u))
      ∙ cong (_+ c · v) (sym (R.·DistL- s h u))

    cosineErrorAlgebra : ∀ s c h u v →
      (c · u - s · v) - (- v) · h ≡ c · u - (s - h) · v
    cosineErrorAlgebra s c h u v =
      cong (λ z → (c · u - s · v) - z)
        (R.-DistL· v h ∙ cong -_ (mulComm v h))
      ∙ cong ((c · u - s · v) +_) (negInvol (h · v))
      ∙ sym (addAssoc (c · u) (- (s · v)) (h · v))
      ∙ cong (c · u +_)
          (cong ((- (s · v)) +_) (sym (negInvol (h · v)))
          ∙ sym (negAdd (s · v) (- (h · v)))
          ∙ cong -_ (sym (R.·DistL- s h v)))

    unitProductBound : ∀ e u bound →
      absℝ e ≤ℝ bound → absℝ u ≤ℝ 1ℝ → absℝ (e · u) ≤ℝ bound
    unitProductBound e u bound e≤bound u≤one =
      subst (_≤ℝ bound) (sym (absMul e u))
        (≤ℝ-trans (absℝ e · absℝ u) (absℝ e · 1ℝ) bound
          (mulPres≤L (absℝ u) 1ℝ (absℝ e)
            (0≤→isNonnegative (absℝ e) (absNonnegative e)) u≤one)
          (subst (_≤ℝ bound) (sym (mulIdR (absℝ e))) e≤bound))

    twoErrorsBound : ∀ e f u v bound →
      absℝ e ≤ℝ bound → absℝ f ≤ℝ bound →
      absℝ u ≤ℝ 1ℝ → absℝ v ≤ℝ 1ℝ →
      absℝ (e · u + f · v) ≤ℝ bound + bound
    twoErrorsBound e f u v bound ep fp up vp =
      ≤ℝ-trans (absℝ (e · u + f · v))
        (absℝ (e · u) + absℝ (f · v)) (bound + bound)
        (absTriangle (e · u) (f · v))
        (addPres≤ (absℝ (e · u)) bound (absℝ (f · v)) bound
          (unitProductBound e u bound ep up)
          (unitProductBound f v bound fp vp))

    sineErrorAtZero : ∀ h →
      ((sinℝ h - sinℝ 0ℝ) - cosℝ 0ℝ · (h - 0ℝ)) ≡ sinℝ h - h
    sineErrorAtZero h = cong₂ _-_
      (cong (λ z → sinℝ h - z) sinℝ-zero ∙ subZero (sinℝ h))
      (cong₂ _·_ cosℝ-zero (subZero h) ∙ mulIdL h)

    cosineErrorAtZero : ∀ h →
      ((cosℝ h - cosℝ 0ℝ) - (- sinℝ 0ℝ) · (h - 0ℝ)) ≡ cosℝ h - 1ℝ
    cosineErrorAtZero h = cong₂ _-_
      (cong (λ z → cosℝ h - z) cosℝ-zero)
      (cong (_· (h - 0ℝ)) (cong -_ sinℝ-zero ∙ negZero)
        ∙ R.0LeftAnnihilates (h - 0ℝ))
      ∙ subZero (cosℝ h - 1ℝ)

    sineErrorTranslation : ∀ x y →
      ((sinℝ y - sinℝ x) - cosℝ x · (y - x)) ≡
      (sinℝ (y - x) - (y - x)) · cosℝ x +
        (cosℝ (y - x) - 1ℝ) · sinℝ x
    sineErrorTranslation x y =
      cong (_- cosℝ x · (y - x)) (sinℝ-difference-expansion x y)
      ∙ sineErrorAlgebra (sinℝ (y - x)) (cosℝ (y - x) - 1ℝ)
          (y - x) (cosℝ x) (sinℝ x)

    cosineErrorTranslation : ∀ x y →
      ((cosℝ y - cosℝ x) - (- sinℝ x) · (y - x)) ≡
      (cosℝ (y - x) - 1ℝ) · cosℝ x +
        (sinℝ (y - x) - (y - x)) · (- sinℝ x)
    cosineErrorTranslation x y =
      cong (_- (- sinℝ x) · (y - x)) (cosℝ-difference-expansion x y)
      ∙ cosineErrorAlgebra (sinℝ (y - x)) (cosℝ (y - x) - 1ℝ)
          (y - x) (cosℝ x) (sinℝ x)
      ∙ cong (((cosℝ (y - x) - 1ℝ) · cosℝ x) +_)
          (sym (R.-DistR· (sinℝ (y - x) - (y - x)) (sinℝ x)))

    displacementClose : ∀ x y δ → x ∼[ δ ] y → 0ℝ ∼[ δ ] (y - x)
    displacementClose x y δ close =
      subst (λ z → z ∼[ δ ] (y - x)) (subSelf x)
        (add-pres∼₁ x y (- x) δ close)

    halfErrorSum : ∀ (ε : ℚ₊) h →
      (rat (fst (ε /2₊)) · h) + (rat (fst (ε /2₊)) · h) ≡ rat (fst ε) · h
    halfErrorSum ε h = sym (mulDistL (rat (fst (ε /2₊))) (rat (fst (ε /2₊))) h)
      ∙ cong (_· h) (rat+rat (fst (ε /2₊)) (fst (ε /2₊))
        ∙ cong rat (1/2∈ℚ./2+/2≡id (fst ε)))

-- Translation by the addition formulas turns the two derivatives at zero
-- into uniform derivatives on all of ℝ. Only two truncated radii are used.
opaque
  trigUniformErrors : ∀ (ε : ℚ₊) →
    ∃[ δ ∈ ℚ₊ ] (∀ x y → x ∼[ δ ] y →
      (absℝ ((sinℝ y - sinℝ x) - cosℝ x · (y - x)) ≤ℝ rat (fst ε) · absℝ (y - x)) ×
      (absℝ ((cosℝ y - cosℝ x) - (- sinℝ x) · (y - x)) ≤ℝ rat (fst ε) · absℝ (y - x)))
  trigUniformErrors ε = do
    (δs , sb) ← sinℝHasDerivative 0ℝ (ε /2₊)
    (δc , cb) ← cosℝHasDerivative 0ℝ (ε /2₊)
    return (min₊ δs δc , λ x y close →
      bounds x y
        (sb (y - x) (displacementClose x y δs
          (M.isMonotone≈≤ x y (min₊ δs δc) δs (min₊≤L δs δc) close)))
        (cb (y - x) (displacementClose x y δc
          (M.isMonotone≈≤ x y (min₊ δs δc) δc (min₊≤R δs δc) close))))
    where
    bounds : ∀ x y →
      absℝ ((sinℝ (y - x) - sinℝ 0ℝ) - cosℝ 0ℝ · ((y - x) - 0ℝ)) ≤ℝ
        rat (fst (ε /2₊)) · absℝ ((y - x) - 0ℝ) →
      absℝ ((cosℝ (y - x) - cosℝ 0ℝ) - (- sinℝ 0ℝ) · ((y - x) - 0ℝ)) ≤ℝ
        rat (fst (ε /2₊)) · absℝ ((y - x) - 0ℝ) →
      (absℝ ((sinℝ y - sinℝ x) - cosℝ x · (y - x)) ≤ℝ rat (fst ε) · absℝ (y - x)) ×
      (absℝ ((cosℝ y - cosℝ x) - (- sinℝ x) · (y - x)) ≤ℝ rat (fst ε) · absℝ (y - x))
    bounds x y sb cb =
      subst2 _≤ℝ_ (sym (cong absℝ (sineErrorTranslation x y))) (halfErrorSum ε (absℝ (y - x)))
        (twoErrorsBound (sinℝ (y - x) - (y - x)) (cosℝ (y - x) - 1ℝ)
          (cosℝ x) (sinℝ x) b sBound cBound (cosℝ-abs≤one x) (sinℝ-abs≤one x))
      , subst2 _≤ℝ_ (sym (cong absℝ (cosineErrorTranslation x y))) (halfErrorSum ε (absℝ (y - x)))
        (twoErrorsBound (cosℝ (y - x) - 1ℝ) (sinℝ (y - x) - (y - x))
          (cosℝ x) (- sinℝ x) b cBound sBound (cosℝ-abs≤one x)
          (subst (_≤ℝ 1ℝ) (sym (absNeg (sinℝ x))) (sinℝ-abs≤one x)))
      where
      b : ℝ
      b = rat (fst (ε /2₊)) · absℝ (y - x)
      sBound : absℝ (sinℝ (y - x) - (y - x)) ≤ℝ b
      sBound = subst2 _≤ℝ_ (cong absℝ (sineErrorAtZero (y - x)))
        (cong (λ z → rat (fst (ε /2₊)) · absℝ z) (subZero (y - x))) sb
      cBound : absℝ (cosℝ (y - x) - 1ℝ) ≤ℝ b
      cBound = subst2 _≤ℝ_ (cong absℝ (cosineErrorAtZero (y - x)))
        (cong (λ z → rat (fst (ε /2₊)) · absℝ z) (subZero (y - x))) cb

  sinℝHasUniformDerivative : IsRadiuswiseUniformDerivative sinℝ cosℝ
  sinℝHasUniformDerivative ε = PT.map (λ (δ , bound) → δ , λ x y p → fst (bound x y p)) (trigUniformErrors ε)

  cosℝHasUniformDerivative : IsRadiuswiseUniformDerivative cosℝ (λ x → - sinℝ x)
  cosℝHasUniformDerivative ε = PT.map (λ (δ , bound) → δ , λ x y p → snd (bound x y p)) (trigUniformErrors ε)
