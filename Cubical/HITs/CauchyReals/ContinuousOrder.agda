module Cubical.HITs.CauchyReals.ContinuousOrder where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.RationalsImports

opaque
  -- Previous name: ≤ContPos'pred.
  continuousClosedLowerComparison :
    {x₀ : ℚ} {f₀ f₁ : ∀ x → rat x₀ ≤ᵣ x → ℝ} →
    IsContinuousWithPred (pred≥ (rat x₀)) f₀ →
    IsContinuousWithPred (pred≥ (rat x₀)) f₁ →
    (∀ u (x₀≤u : x₀ ℚ.≤ u) →
      f₀ (rat u) (≤ℚ→≤ᵣ x₀ u x₀≤u) ≤ᵣ
      f₁ (rat u) (≤ℚ→≤ᵣ x₀ u x₀≤u)) →
    ∀ x (x₀≤x : rat x₀ ≤ᵣ x) → f₀ x x₀≤x ≤ᵣ f₁ x x₀≤x
  continuousClosedLowerComparison {x₀} {f₀} {f₁} f₀C f₁C compare x x₀≤x =
    subst2 _≤ᵣ_
      (cong (uncurry f₀) (clampPoint≡ x x₀≤x))
      (cong (uncurry f₁) (clampPoint≡ x x₀≤x))
      (≤Cont clamped₀-cont clamped₁-cont compare-rat x)
    where
    clampPoint : ℝ → Σ[ y ∈ ℝ ] rat x₀ ≤ᵣ y
    clampPoint y = maxᵣ (rat x₀) y , ≤maxᵣ (rat x₀) y

    clampPoint≡ : ∀ y (x₀≤y : rat x₀ ≤ᵣ y) →
      clampPoint y ≡ (y , x₀≤y)
    clampPoint≡ y x₀≤y =
      Σ≡Prop (λ z → isProp≤ᵣ (rat x₀) z)
        (≤→maxᵣ (rat x₀) y x₀≤y)

    clampRatPoint≡ : ∀ u →
      clampPoint (rat u) ≡
        (rat (ℚ.max x₀ u) , ≤ℚ→≤ᵣ x₀ (ℚ.max x₀ u) (ℚ.≤max x₀ u))
    clampRatPoint≡ u =
      Σ≡Prop (λ z → isProp≤ᵣ (rat x₀) z) (maxᵣ-rat x₀ u)

    clamped₀ : ℝ → ℝ
    clamped₀ = uncurry f₀ ∘ clampPoint

    clamped₁ : ℝ → ℝ
    clamped₁ = uncurry f₁ ∘ clampPoint

    clamped₀-cont : IsContinuous clamped₀
    clamped₀-cont =
      IsContinuousWithPred∘IsContinuous (pred≥ (rat x₀)) f₀
        (maxᵣ (rat x₀)) (λ y → ≤maxᵣ (rat x₀) y)
        f₀C (IsContinuousMaxL (rat x₀))

    clamped₁-cont : IsContinuous clamped₁
    clamped₁-cont =
      IsContinuousWithPred∘IsContinuous (pred≥ (rat x₀)) f₁
        (maxᵣ (rat x₀)) (λ y → ≤maxᵣ (rat x₀) y)
        f₁C (IsContinuousMaxL (rat x₀))

    compare-rat : ∀ u → clamped₀ (rat u) ≤ᵣ clamped₁ (rat u)
    compare-rat u =
      subst2 _≤ᵣ_
        (sym (cong (uncurry f₀) (clampRatPoint≡ u)))
        (sym (cong (uncurry f₁) (clampRatPoint≡ u)))
        (compare (ℚ.max x₀ u) (ℚ.≤max x₀ u))

opaque
  unfolding _<ᵣ_
  -- Previous name: <→≤ContPos'pred.
  continuousOpenLowerComparison :
    {x₀ : ℚ} {f₀ f₁ : ∀ x → rat x₀ <ᵣ x → ℝ} →
    IsContinuousWithPred (pred> (rat x₀)) f₀ →
    IsContinuousWithPred (pred> (rat x₀)) f₁ →
    (∀ u (x₀<u : rat x₀ <ᵣ rat u) →
      f₀ (rat u) x₀<u ≤ᵣ f₁ (rat u) x₀<u) →
    ∀ x (x₀<x : rat x₀ <ᵣ x) → f₀ x x₀<x ≤ᵣ f₁ x x₀<x
  continuousOpenLowerComparison {x₀} {f₀} {f₁} f₀C f₁C compare x x₀<x =
    PT.rec (isProp≤ᵣ _ _)
      (λ ((q , q') , (x₀≤q , q<q' , q'≤x)) →
        let
          x₀<q' : rat x₀ <ᵣ rat q'
          x₀<q' =
            <ℚ→<ᵣ x₀ q'
              (ℚ.isTrans≤< x₀ q q' (≤ᵣ→≤ℚ x₀ q x₀≤q) q<q')

          q'≤z→x₀<z : pred≥ (rat q') ⊆ pred> (rat x₀)
          q'≤z→x₀<z z q'≤z = isTrans<≤ᵣ (rat x₀) (rat q') z x₀<q' q'≤z

          restricted₀ =
            IsContinuousWithPred⊆
              (pred> (rat x₀)) (pred≥ (rat q')) f₀ q'≤z→x₀<z f₀C

          restricted₁ =
            IsContinuousWithPred⊆
              (pred> (rat x₀)) (pred≥ (rat q')) f₁ q'≤z→x₀<z f₁C

          result = continuousClosedLowerComparison {q'}
            restricted₀ restricted₁
            (λ u q'≤u →
              compare u
                (q'≤z→x₀<z (rat u) (≤ℚ→≤ᵣ q' u q'≤u)))
            x q'≤x
        in
        subst (λ x₀<x → f₀ x x₀<x ≤ᵣ f₁ x x₀<x)
          (isProp<ᵣ _ _ _ _) result)
      x₀<x

opaque
  unfolding minᵣ maxᵣ
  continuousClosedIntervalComparison :
    {x₀ x₁ : ℚ} → x₀ ℚ.≤ x₁ →
    {f₀ f₁ : ∀ x → x ∈ intervalℙ (rat x₀) (rat x₁) → ℝ} →
    IsContinuousWithPred (intervalℙ (rat x₀) (rat x₁)) f₀ →
    IsContinuousWithPred (intervalℙ (rat x₀) (rat x₁)) f₁ →
    (∀ u (u∈ : rat u ∈ intervalℙ (rat x₀) (rat x₁)) →
      f₀ (rat u) u∈ ≤ᵣ f₁ (rat u) u∈) →
    ∀ x (x∈ : x ∈ intervalℙ (rat x₀) (rat x₁)) →
      f₀ x x∈ ≤ᵣ f₁ x x∈
  continuousClosedIntervalComparison {x₀} {x₁} x₀≤x₁
      {f₀} {f₁} f₀C f₁C compare x x∈ =
    subst (λ (u , u∈) → f₀ u u∈ ≤ᵣ f₁ u u∈)
      (Σ≡Prop (∈-isProp (intervalℙ (rat x₀) (rat x₁)))
        (sym (∈ℚintervalℙ→clampᵣ≡ _ _ _ x∈)))
      (≤Cont {clamped₀} {clamped₁}
        clamped₀-cont clamped₁-cont compare-rat x)
    where
    clamped₀ : ℝ → ℝ
    clamped₀ z =
      f₀ (clampᵣ (rat x₀) (rat x₁) z)
        (clampᵣ∈ℚintervalℙ _ _ (≤ℚ→≤ᵣ x₀ x₁ x₀≤x₁) z)

    clamped₁ : ℝ → ℝ
    clamped₁ z =
      f₁ (clampᵣ (rat x₀) (rat x₁) z)
        (clampᵣ∈ℚintervalℙ _ _ (≤ℚ→≤ᵣ x₀ x₁ x₀≤x₁) z)

    clamped₀-cont : IsContinuous clamped₀
    clamped₀-cont =
      IsContinuousWithPred∘IsContinuous
        (intervalℙ (rat x₀) (rat x₁)) f₀
        (clampᵣ (rat x₀) (rat x₁))
        (clampᵣ∈ℚintervalℙ _ _ (≤ℚ→≤ᵣ x₀ x₁ x₀≤x₁)) f₀C
        (IsContinuousClamp (rat x₀) (rat x₁))

    clamped₁-cont : IsContinuous clamped₁
    clamped₁-cont =
      IsContinuousWithPred∘IsContinuous
        (intervalℙ (rat x₀) (rat x₁)) f₁
        (clampᵣ (rat x₀) (rat x₁))
        (clampᵣ∈ℚintervalℙ _ _ (≤ℚ→≤ᵣ x₀ x₁ x₀≤x₁)) f₁C
        (IsContinuousClamp (rat x₀) (rat x₁))

    compare-rat : ∀ u → clamped₀ (rat u) ≤ᵣ clamped₁ (rat u)
    compare-rat u =
      let
        I = intervalℙ (rat x₀) (rat x₁)
        cl∈ = clampᵣ∈ℚintervalℙ
          (rat x₀) (rat x₁) (≤ℚ→≤ᵣ x₀ x₁ x₀≤x₁) (rat u)
        cl≡ = clampᵣ-rat x₀ x₁ u
      in
      subst (λ (v , v∈) → f₀ v v∈ ≤ᵣ f₁ v v∈)
        (Σ≡Prop (∈-isProp I) (sym cl≡))
        (compare (ℚ.clamp x₀ x₁ u) (subst (_∈ I) cl≡ cl∈))
