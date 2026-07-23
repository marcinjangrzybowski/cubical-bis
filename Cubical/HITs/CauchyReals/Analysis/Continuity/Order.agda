module Cubical.HITs.CauchyReals.Analysis.Continuity.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness using
  (isSetℝ)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Predicate
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp using
  (IsContinuousClamp; ∈ℚintervalℙ→clampᵣ≡; clampᵣ∈intervalℙ)
open import Cubical.HITs.CauchyReals.Algebra.Order.Apartness using
  (_＃_; 0＃ₚ; isOpenPred0＃)
open import Cubical.HITs.CauchyReals.Algebra.Order.Lattice using
  (<min-lem; min≤ᵣ; ≤→minᵣ; max<-lem; ≤maxᵣ; ≤→maxᵣ)
open import Cubical.HITs.CauchyReals.Foundation.Rationals


opaque
  unfolding _≤ᵣ_ NonExpanding₂.go

  -- Previous location: Continuity.Base.
  ≤Cont₂ : {f₀ f₁ : ℝ → ℝ → ℝ}
    → IsContinuous₂ f₀
    → IsContinuous₂ f₁
    → (∀ u u' → f₀ (rat u) (rat u') ≤ᵣ f₁ (rat u) (rat u'))
    → ∀ x x' → f₀ x x' ≤ᵣ f₁ x x'
  ≤Cont₂ f₀C f₁C = ≡Cont₂ (contNE₂∘ maxR f₀C f₁C) f₁C


  -- Previous location: Continuity.Base.
  ≤Cont : {f₀ f₁ : ℝ → ℝ}
    → IsContinuous f₀
    → IsContinuous f₁
    → (∀ u → f₀ (rat u) ≤ᵣ f₁ (rat u))
    → ∀ x → f₀ x ≤ᵣ f₁ x
  ≤Cont f₀C f₁C =
    ≡Continuous _ _ (contDiagNE₂ maxR _ _ f₀C f₁C) f₁C


  -- Previous location: Continuity.Base.
  ≤Cont₂Pos : {f₀ f₁ : ℝ → ℝ → ℝ}
    → IsContinuous₂ f₀
    → IsContinuous₂ f₁
    → (∀ u u' → 0 ℚ.≤ u → 0 ℚ.≤ u' →
      f₀ (rat u) (rat u') ≤ᵣ f₁ (rat u) (rat u'))
    → ∀ x x' → 0 ≤ᵣ x → 0 ≤ᵣ x' → f₀ x x' ≤ᵣ f₁ x x'
  ≤Cont₂Pos {f₀} {f₁} f₀C f₁C compare x x' 0≤x 0≤x' =
    subst2 (λ y y' → f₀ y y' ≤ᵣ f₁ y y') 0≤x 0≤x'
      (≤Cont₂
        (cont₂∘ f₀C (IsContinuousMaxL 0) (IsContinuousMaxL 0))
        (cont₂∘ f₁C (IsContinuousMaxL 0) (IsContinuousMaxL 0))
        (λ u u' → compare _ _ (ℚ.≤max 0 u) (ℚ.≤max 0 u'))
        x x')


  -- Previous location: Continuity.Base.
  ≤ContPos' : {x₀ : ℚ} {f₀ f₁ : ℝ → ℝ}
    → IsContinuous f₀
    → IsContinuous f₁
    → (∀ u → x₀ ℚ.≤ u → f₀ (rat u) ≤ᵣ f₁ (rat u))
    → ∀ x → rat x₀ ≤ᵣ x → f₀ x ≤ᵣ f₁ x
  ≤ContPos' {x₀} {f₀} {f₁} f₀C f₁C compare x x₀≤x =
    subst (λ y → f₀ y ≤ᵣ f₁ y) x₀≤x
      (≤Cont
        (IsContinuous∘ _ _ f₀C (IsContinuousMaxL (rat x₀)))
        (IsContinuous∘ _ _ f₁C (IsContinuousMaxL (rat x₀)))
        (λ u → compare _ (ℚ.≤max x₀ u)) x)


  -- Previous location: Continuity.Base.
  <→≤ContPos' : {x₀ : ℚ} {f₀ f₁ : ℝ → ℝ}
    → IsContinuous f₀
    → IsContinuous f₁
    → (∀ u → x₀ ℚ.< u → f₀ (rat u) ≤ᵣ f₁ (rat u))
    → ∀ x → rat x₀ <ᵣ x → f₀ x ≤ᵣ f₁ x
  <→≤ContPos' {x₀} {f₀} {f₁} f₀C f₁C compare x =
    PT.rec (isSetℝ _ _)
      (λ ((q , q') , (x₀≤q , q<q' , q'≤x)) →
        ≤ContPos' {q'} f₀C f₁C
          ((_∘ ℚ.isTrans<≤ _ _ _
            (ℚ.isTrans≤< _ _ _ (≤ᵣ→≤ℚ _ _ x₀≤q) q<q'))
            ∘ compare)
          x q'≤x)


-- Previous location: Continuity.Base.
≤ContPos : {f₀ f₁ : ℝ → ℝ}
  → IsContinuous f₀
  → IsContinuous f₁
  → (∀ u → 0 ℚ.≤ u → f₀ (rat u) ≤ᵣ f₁ (rat u))
  → ∀ x → 0 ≤ᵣ x → f₀ x ≤ᵣ f₁ x
≤ContPos = ≤ContPos' {0}


opaque
  unfolding _≤ᵣ_ minᵣ maxᵣ NonExpanding₂.go

  -- Previous location: Algebra.Inverse.
  ≤ContWP : ∀ {P f₀ f₁} → ⟨ openPred P ⟩
    → IsContinuousWithPred P f₀
    → IsContinuousWithPred P f₁
    → (∀ u u∈ → f₀ (rat u) u∈ ≤ᵣ f₁ (rat u) u∈)
    → ∀ x x∈ → f₀ x x∈ ≤ᵣ f₁ x x∈
  ≤ContWP {P} {f₀} {f₁} oP f₀C f₁C X x x∈ =
    ≡ContinuousWithPred P P oP oP _ _
      (contDiagNE₂WP maxR P _ _ f₀C f₁C)
      f₁C
      (λ r r∈ r∈' →
        X _ _ ∙ cong (f₁ (rat r)) (∈-isProp P _ r∈ r∈'))
      x x∈ x∈


  -- Previous location: Algebra.Inverse.
  ≤ContWP＃≤ : ∀ {f₀ f₁} q → 0 ℚ.< q
    → IsContinuousWithPred 0＃ₚ f₀
    → IsContinuousWithPred 0＃ₚ f₁
    → (∀ u u∈ → u ℚ.≤ q → f₀ (rat u) u∈ ≤ᵣ f₁ (rat u) u∈)
    → ∀ x x∈ → x ≤ᵣ rat q → f₀ x x∈ ≤ᵣ f₁ x x∈
  ≤ContWP＃≤ {f₀} {f₁} q 0<q f₀C f₁C X x x∈ x≤q =
    let
      ＃min : ∀ r → 0 ＃ r → 0 ＃ minᵣ r (rat q)
      ＃min r = ⊎.map
        (λ 0<r → <min-lem _ _ 0 0<r (<ℚ→<ᵣ _ _ 0<q))
        (λ r<0 →
          isTrans≤<ᵣ (minᵣ r (rat q)) r _ (min≤ᵣ r (rat q)) r<0)

      z = ≤ContWP
        {0＃ₚ}
        {λ r z → f₀ (minᵣ r (rat q)) (＃min r z)}
        {λ r z → f₁ (minᵣ r (rat q)) (＃min r z)}
        isOpenPred0＃
        (IsContinuousWP∘ 0＃ₚ 0＃ₚ _ _ _ f₀C
          (AsContinuousWithPred 0＃ₚ _ (IsContinuousMinR _)))
        (IsContinuousWP∘ 0＃ₚ 0＃ₚ _ _ _ f₁C
          (AsContinuousWithPred 0＃ₚ _ (IsContinuousMinR _)))
        (λ u u∈ → X (ℚ.min u q) (＃min (rat u) u∈) (ℚ.min≤' u _))
        x x∈
    in
    subst {A = Σ _ (_∈ 0＃ₚ)}
      (λ (x , x∈) → f₀ x x∈ ≤ᵣ f₁ x x∈)
      (Σ≡Prop (∈-isProp 0＃ₚ) (≤→minᵣ _ _ x≤q)) z


  -- Previous location: Algebra.Inverse.
  ≤ContWP＃≤' : ∀ {f₀ f₁} q → q ℚ.< 0
    → IsContinuousWithPred 0＃ₚ f₀
    → IsContinuousWithPred 0＃ₚ f₁
    → (∀ u u∈ → q ℚ.≤ u → f₀ (rat u) u∈ ≤ᵣ f₁ (rat u) u∈)
    → ∀ x x∈ → rat q ≤ᵣ x → f₀ x x∈ ≤ᵣ f₁ x x∈
  ≤ContWP＃≤' {f₀} {f₁} q q<0 f₀C f₁C X x x∈ q≤x =
    let
      ＃max : ∀ r → 0 ＃ r → 0 ＃ maxᵣ r (rat q)
      ＃max r = ⊎.map
        (λ 0<r → isTrans<≤ᵣ 0 _ _ 0<r (≤maxᵣ r (rat q)))
        (λ r<0 → max<-lem r (rat q) _ r<0 (<ℚ→<ᵣ _ _ q<0))

      z = ≤ContWP
        {0＃ₚ}
        {λ r z → f₀ (maxᵣ r (rat q)) (＃max r z)}
        {λ r z → f₁ (maxᵣ r (rat q)) (＃max r z)}
        isOpenPred0＃
        (IsContinuousWP∘ 0＃ₚ 0＃ₚ _ _ _ f₀C
          (AsContinuousWithPred 0＃ₚ _ (IsContinuousMaxR _)))
        (IsContinuousWP∘ 0＃ₚ 0＃ₚ _ _ _ f₁C
          (AsContinuousWithPred 0＃ₚ _ (IsContinuousMaxR _)))
        (λ u u∈ → X (ℚ.max u q) (＃max (rat u) u∈) (ℚ.≤max' u q))
        x x∈
    in
    subst {A = Σ _ (_∈ 0＃ₚ)}
      (λ (x , x∈) → f₀ x x∈ ≤ᵣ f₁ x x∈)
      (Σ≡Prop (∈-isProp 0＃ₚ)
        (maxᵣComm x (rat q) ∙ ≤→maxᵣ (rat q) _ q≤x)) z

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
        (clampᵣ∈intervalℙ _ _ (≤ℚ→≤ᵣ x₀ x₁ x₀≤x₁) z)

    clamped₁ : ℝ → ℝ
    clamped₁ z =
      f₁ (clampᵣ (rat x₀) (rat x₁) z)
        (clampᵣ∈intervalℙ _ _ (≤ℚ→≤ᵣ x₀ x₁ x₀≤x₁) z)

    clamped₀-cont : IsContinuous clamped₀
    clamped₀-cont =
      IsContinuousWithPred∘IsContinuous
        (intervalℙ (rat x₀) (rat x₁)) f₀
        (clampᵣ (rat x₀) (rat x₁))
        (clampᵣ∈intervalℙ _ _ (≤ℚ→≤ᵣ x₀ x₁ x₀≤x₁)) f₀C
        (IsContinuousClamp (rat x₀) (rat x₁))

    clamped₁-cont : IsContinuous clamped₁
    clamped₁-cont =
      IsContinuousWithPred∘IsContinuous
        (intervalℙ (rat x₀) (rat x₁)) f₁
        (clampᵣ (rat x₀) (rat x₁))
        (clampᵣ∈intervalℙ _ _ (≤ℚ→≤ᵣ x₀ x₁ x₀≤x₁)) f₁C
        (IsContinuousClamp (rat x₀) (rat x₁))

    compare-rat : ∀ u → clamped₀ (rat u) ≤ᵣ clamped₁ (rat u)
    compare-rat u =
      let
        I = intervalℙ (rat x₀) (rat x₁)
        cl∈ = clampᵣ∈intervalℙ
          (rat x₀) (rat x₁) (≤ℚ→≤ᵣ x₀ x₁ x₀≤x₁) (rat u)
        cl≡ = clampᵣ-rat x₀ x₁ u
      in
      subst (λ (v , v∈) → f₀ v v∈ ≤ᵣ f₁ v v∈)
        (Σ≡Prop (∈-isProp I) (sym cl≡))
        (compare (ℚ.clamp x₀ x₁ u) (subst (_∈ I) cl≡ cl∈))
