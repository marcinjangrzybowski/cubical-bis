module Cubical.HITs.CauchyReals.ArcSin.Prelim.Monotone.Quarter where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Trigonometry.Base
open import Cubical.HITs.CauchyReals.Trigonometry.Pi

open import Cubical.HITs.CauchyReals.ArcSin.Prelim.Basic

opaque
  sin-firstQuarter-strictMonotone :
        (x y : ℝ)
        (x∈ : x ∈ intervalℙ 0 π-number/2)
        (y∈ : y ∈ intervalℙ 0 π-number/2)
        → x <ᵣ y → sin x <ᵣ sin y
  sin-firstQuarter-strictMonotone x y x∈ y∈ x<y =
    let (y' , x<y' , y'<y)  = denseℝ _ _ x<y
        y'∈ = y'∈interval y' x<y' y'<y
    in isTrans<≤ᵣ _ _ _
         (0<y-x→x<y _ _ (sin-diff-positive y' x<y' y'<y))
         (sin-firstQuarter-Monotone y' y
           y'∈ y∈
           (<ᵣWeaken≤ᵣ _ _ y'<y))
    where
    y'∈interval : ∀ y' → x <ᵣ y' → y' <ᵣ y → y' ∈ intervalℙ 0 π-number/2
    y'∈interval y' x<y' y'<y =
      isTrans≤ᵣ _ _ _ (fst x∈) (<ᵣWeaken≤ᵣ _ _ x<y') ,
      <ᵣWeaken≤ᵣ _ _ (isTrans<≤ᵣ _ _ _ y'<y (snd y∈))

    cos-positive : ∀ y' → x <ᵣ y' → y' <ᵣ y → 0 <ᵣ cos y'
    cos-positive y' x<y' y'<y =
      0≤x<π/2→0<cos[x] y'
        (isTrans≤ᵣ _ _ _ (fst x∈) (<ᵣWeaken≤ᵣ _ _ x<y'))
        (isTrans<≤ᵣ _ _ _ y'<y (snd y∈))

    product-positive : ∀ y' → x <ᵣ y' → y' <ᵣ y →
      0 <ᵣ cos y' ·ᵣ (y' -ᵣ x)
    product-positive y' x<y' y'<y =
      snd ((cos y' , cos-positive y' x<y' y'<y)
        ₊·ᵣ (y' -ᵣ x , x<y→0<y-x _ _ x<y'))

    cos-lower : ∀ y' → x <ᵣ y' → y' <ᵣ y →
      ∀ x' → x ≤ᵣ x' → x' ≤ᵣ y' → cos y' ≤ᵣ cos x'
    cos-lower y' x<y' y'<y x' ≤x' x'≤ =
      cos-firstQuarter-Monotone x' y'
        (isTrans≤ᵣ _ _ _ (fst x∈) ≤x' ,
         isTrans≤ᵣ _ _ _ x'≤ (snd (y'∈interval y' x<y' y'<y)))
        (y'∈interval y' x<y' y'<y)
        x'≤

    integral-lower : ∀ y' → x <ᵣ y' → y' <ᵣ y →
      cos y' ·ᵣ (y' -ᵣ x) ≤ᵣ sin y' -ᵣ sin x
    integral-lower y' x<y' y'<y =
      Integral-≤ x y' (<ᵣWeaken≤ᵣ _ _ x<y')
        (λ _ _ _ → cos y')
        (λ x' _ _ → cos x')
        (cos y' ·ᵣ (y' -ᵣ x))
        (sin y' -ᵣ sin x)
        (cos-lower y' x<y' y'<y)
        (IntegralConstℙ x y' (<ᵣWeaken≤ᵣ _ _ x<y') (cos y'))
        (∫cos x y' (<ᵣWeaken≤ᵣ _ _ x<y'))

    sin-diff-positive : ∀ y' → x <ᵣ y' → y' <ᵣ y →
      0 <ᵣ sin y' -ᵣ sin x
    sin-diff-positive y' x<y' y'<y =
      isTrans<≤ᵣ _ _ _
        (product-positive y' x<y' y'<y)
        (integral-lower y' x<y' y'<y)
