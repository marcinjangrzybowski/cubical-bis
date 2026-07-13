module Cubical.HITs.CauchyReals.InverseDerivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.RationalsImports
open import Cubical.HITs.CauchyReals.Derivative hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.InverseLipschitz

open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

private
  opaque
    rat-·₊ : ∀ u v → rat (fst (u ·₊ v)) ≡ rat (fst u) ·ᵣ rat (fst v)
    rat-·₊ u v =
      let p : fst (u ·₊ v) ≡ fst u ℚ.· fst v
          p = ℚ!
      in cong rat p ∙ rat·ᵣrat (fst u) (fst v)

-- Previous name: invDerivativeℙ, for the quotient-slope derivative.
inverseDerivativeℙ :
  ∀ (P Q : ℙ ℝ)
    (f f' : ∀ x → x ∈ P → ℝ)
    (g : ∀ y → y ∈ Q → ℝ)
    (g∈P : ∀ y y∈ → g y y∈ ∈ P)
    (section : ∀ y y∈ → f (g y y∈) (g∈P y y∈) ≡ y)
    (m : ℚ₊)
  → LowerLipschitz-ℝ→ℝℙ m P f
  → (f'＃ : ∀ x x∈ → 0 ＃ f' x x∈)
  → DerivativeOfℙ P , f is f'
  → DerivativeOfℙ Q , g is
      (λ y y∈ → invℝ (f' (g y y∈) (g∈P y y∈))
        (f'＃ (g y y∈) (g∈P y y∈)))
inverseDerivativeℙ P Q f f' g g∈P section m lower f'＃ df x x∈ ε =
  PT.rec squash₁
    chooseModulus
    (denseℚinℝ 0 (fst ηBound) (snd ηBound))
  where
  gx : ℝ
  gx = g x x∈

  gx∈ : gx ∈ P
  gx∈ = g∈P x x∈

  d : ℝ
  d = f' gx gx∈

  d＃ : 0 ＃ d
  d＃ = f'＃ gx gx∈

  d⁻¹ : ℝ
  d⁻¹ = invℝ d d＃

  denominator : ℝ₊
  denominator =
    absᵣ d⁻¹ +ᵣ 1 ,
      isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _))
        (≤<ᵣMonotone+ᵣ 0 (absᵣ d⁻¹) 0 1
          (0≤absᵣ d⁻¹) (decℚ<ᵣ? {0} {1}))

  εm : ℝ₊
  εm = ℚ₊→ℝ₊ ε ₊·ᵣ ℚ₊→ℝ₊ m

  ηBound : ℝ₊
  ηBound = εm ₊·ᵣ invℝ₊ denominator

  estimate :
    (q : ℚ) → 0 <ᵣ rat q → rat q <ᵣ fst ηBound →
    (δ : ℚ₊) →
    (∀ y y∈ → absᵣ (y -ᵣ gx) ≤ᵣ rat (fst δ) →
      absᵣ (derivativeErrorℙ P f f' gx gx∈ y y∈)
      ≤ᵣ rat q ·ᵣ absᵣ (y -ᵣ gx)) →
    ∀ y y∈ → absᵣ (y -ᵣ x) ≤ᵣ rat (fst (m ·₊ δ)) →
    absᵣ (derivativeErrorℙ Q g
      (λ u u∈ → invℝ (f' (g u u∈) (g∈P u u∈)) (f'＃ _ _))
      x x∈ y y∈)
    ≤ᵣ rat (fst ε) ·ᵣ absᵣ (y -ᵣ x)
  estimate q 0<q q<ηBound δ D y y∈ y-x≤mδ =
    isTrans≡≤ᵣ _ _ _ errorAbsPath
      (isTrans≤ᵣ _ _ _
        (≤ᵣ-o·ᵣ _ _ (absᵣ d⁻¹) (0≤absᵣ d⁻¹)
          (D gy gy∈ gy-gx≤δ))
        (isTrans≡≤ᵣ _ _ _ ℝ!
          (isTrans≤ᵣ _ _ _
            (≤ᵣ-·ᵣo
              (absᵣ d⁻¹ ·ᵣ rat q)
              (rat (fst ε) ·ᵣ rat (fst m))
              (absᵣ (gy -ᵣ gx))
              (0≤absᵣ (gy -ᵣ gx)) coefficient≤)
            (isTrans≡≤ᵣ _ _ _ ℝ!
              (≤ᵣ-o·ᵣ _ _ (rat (fst ε))
                (<ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ ε)))
                forwardLower)))))
    where
    gy : ℝ
    gy = g y y∈

    gy∈ : gy ∈ P
    gy∈ = g∈P y y∈

    forwardLower :
      rat (fst m) ·ᵣ absᵣ (gy -ᵣ gx) ≤ᵣ absᵣ (y -ᵣ x)
    forwardLower =
      isTrans≤≡ᵣ _ _ _
        (lower gy gy∈ gx gx∈)
        (cong absᵣ (cong₂ _-ᵣ_ (section y y∈) (section x x∈)))

    m·gy-gx≤m·δ :
      rat (fst m) ·ᵣ absᵣ (gy -ᵣ gx) ≤ᵣ
      rat (fst m) ·ᵣ rat (fst δ)
    m·gy-gx≤m·δ =
      isTrans≤≡ᵣ _ _ _
        (isTrans≤ᵣ _ _ _ forwardLower y-x≤mδ)
        (rat-·₊ m δ)

    gy-gx≤δ : absᵣ (gy -ᵣ gx) ≤ᵣ rat (fst δ)
    gy-gx≤δ =
      invEq
        (z≤x≃y₊·z≤y₊·x
          (rat (fst δ)) (absᵣ (gy -ᵣ gx)) (ℚ₊→ℝ₊ m))
        m·gy-gx≤m·δ

    E : ℝ
    E = derivativeErrorℙ P f f' gx gx∈ gy gy∈

    inverseErrorPath :
      derivativeErrorℙ Q g
        (λ u u∈ → invℝ (f' (g u u∈) (g∈P u u∈)) (f'＃ _ _))
        x x∈ y y∈
      ≡ -ᵣ d⁻¹ ·ᵣ E
    inverseErrorPath =
      cong (λ Δ → gy -ᵣ gx -ᵣ d⁻¹ ·ᵣ Δ)
        (cong₂ _-ᵣ_ (sym (section y y∈)) (sym (section x x∈)))
      ∙ ℝ!
      ∙ cong (λ t → (-ᵣ d⁻¹ ·ᵣ (f gy gy∈ -ᵣ f gx gx∈))
                       +ᵣ t ·ᵣ (gy -ᵣ gx))
          (sym (x·invℝ[x] d d＃))
      ∙ ℝ!

    errorAbsPath :
      absᵣ (derivativeErrorℙ Q g
        (λ u u∈ → invℝ (f' (g u u∈) (g∈P u u∈)) (f'＃ _ _))
        x x∈ y y∈)
      ≡ absᵣ d⁻¹ ·ᵣ absᵣ E
    errorAbsPath =
      cong absᵣ inverseErrorPath
      ∙ ·absᵣ (-ᵣ d⁻¹) E
      ∙ cong (_·ᵣ absᵣ E) (sym (-absᵣ d⁻¹))

    absd⁻¹≤denominator : absᵣ d⁻¹ ≤ᵣ fst denominator
    absd⁻¹≤denominator =
      isTrans≡≤ᵣ _ _ _ (sym (+IdR (absᵣ d⁻¹)))
        (≤ᵣ-o+ 0 1 (absᵣ d⁻¹) decℚ≤ᵣ?)

    denominator·q≤εm : fst denominator ·ᵣ rat q ≤ᵣ fst εm
    denominator·q≤εm =
      <ᵣWeaken≤ᵣ _ _
        (fst (z<x/y₊≃y₊·z<x (fst εm) (rat q) denominator)
          q<ηBound)

    coefficient≤ :
      absᵣ d⁻¹ ·ᵣ rat q ≤ᵣ rat (fst ε) ·ᵣ rat (fst m)
    coefficient≤ =
      isTrans≤≡ᵣ _ _ _
        (isTrans≤ᵣ _ _ _
          (≤ᵣ-·ᵣo (absᵣ d⁻¹) (fst denominator) (rat q)
            (<ᵣWeaken≤ᵣ _ _ 0<q) absd⁻¹≤denominator)
          denominator·q≤εm)
        refl

  chooseModulus :
    Σ[ q ∈ ℚ ] (0 <ᵣ rat q) × (rat q <ᵣ fst ηBound) →
    ∃[ δ ∈ ℚ₊ ]
      (∀ y y∈ → absᵣ (y -ᵣ x) ≤ᵣ rat (fst δ) →
        absᵣ (derivativeErrorℙ Q g
          (λ u u∈ → invℝ (f' (g u u∈) (g∈P u u∈)) (f'＃ _ _))
          x x∈ y y∈)
        ≤ᵣ rat (fst ε) ·ᵣ absᵣ (y -ᵣ x))
  chooseModulus (q , 0<q , q<ηBound) =
    PT.map
      (λ (δ , D) →
        m ·₊ δ , λ y y∈ y-x≤mδ →
          estimate q 0<q q<ηBound δ D y y∈ y-x≤mδ)
      (df gx gx∈ (q , <ᵣ→<ℚ 0 q 0<q))

inverse-uDerivativeℙ :
  ∀ (P Q : ℙ ℝ)
    (f f' : ∀ x → x ∈ P → ℝ)
    (g : ∀ y → y ∈ Q → ℝ)
    (g∈P : ∀ y y∈ → g y y∈ ∈ P)
    (section : ∀ y y∈ → f (g y y∈) (g∈P y y∈) ≡ y)
    (m M : ℚ₊)
  → LowerLipschitz-ℝ→ℝℙ m P f
  → (f'＃ : ∀ x x∈ → 0 ＃ f' x x∈)
  → (∀ x x∈ →
      absᵣ (invℝ (f' x x∈) (f'＃ x x∈)) ≤ᵣ rat (fst M))
  → uDerivativeOfℙ P , f is f'
  → uDerivativeOfℙ Q , g is
      (λ y y∈ → invℝ (f' (g y y∈) (g∈P y y∈))
        (f'＃ (g y y∈) (g∈P y y∈)))
inverse-uDerivativeℙ P Q f f' g g∈P section m M lower f'＃ invBound df ε =
  PT.rec squash₁ chooseEta
    (denseℚinℝ 0 (fst ηBound) (snd ηBound))
  where
  denominator : ℝ₊
  denominator =
    rat (fst M) +ᵣ 1 ,
      isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _))
        (≤<ᵣMonotone+ᵣ 0 (rat (fst M)) 0 1
          (<ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ M)))
          (decℚ<ᵣ? {0} {1}))

  εm : ℝ₊
  εm = ℚ₊→ℝ₊ ε ₊·ᵣ ℚ₊→ℝ₊ m

  ηBound : ℝ₊
  ηBound = εm ₊·ᵣ invℝ₊ denominator

  ratM≤denominator : rat (fst M) ≤ᵣ fst denominator
  ratM≤denominator =
    isTrans≡≤ᵣ _ _ _ (sym (+IdR (rat (fst M))))
      (≤ᵣ-o+ 0 1 (rat (fst M)) decℚ≤ᵣ?)

  estimate :
    (q : ℚ) → 0 <ᵣ rat q → rat q <ᵣ fst ηBound →
    (δ : ℚ₊) →
    (∀ x x∈ y y∈ → absᵣ (y -ᵣ x) ≤ᵣ rat (fst δ) →
      absᵣ (derivativeErrorℙ P f f' x x∈ y y∈)
      ≤ᵣ rat q ·ᵣ absᵣ (y -ᵣ x)) →
    ∀ x x∈ y y∈ → absᵣ (y -ᵣ x) ≤ᵣ rat (fst (m ·₊ δ)) →
    absᵣ (derivativeErrorℙ Q g
      (λ u u∈ → invℝ (f' (g u u∈) (g∈P u u∈)) (f'＃ _ _))
      x x∈ y y∈)
    ≤ᵣ rat (fst ε) ·ᵣ absᵣ (y -ᵣ x)
  estimate q 0<q q<ηBound δ D x x∈ y y∈ y-x≤mδ =
    isTrans≡≤ᵣ _ _ _ errorAbsPath
      (isTrans≤ᵣ _ _ _
        (≤ᵣ-o·ᵣ _ _ (absᵣ d⁻¹) (0≤absᵣ d⁻¹)
          (D gx gx∈ gy gy∈ gy-gx≤δ))
        (isTrans≡≤ᵣ _ _ _ ℝ!
          (isTrans≤ᵣ _ _ _
            (≤ᵣ-·ᵣo
              (absᵣ d⁻¹ ·ᵣ rat q)
              (rat (fst ε) ·ᵣ rat (fst m))
              (absᵣ (gy -ᵣ gx))
              (0≤absᵣ (gy -ᵣ gx)) coefficient≤)
            (isTrans≡≤ᵣ _ _ _ ℝ!
              (≤ᵣ-o·ᵣ _ _ (rat (fst ε))
                (<ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ ε)))
                forwardLower)))))
    where
    gx : ℝ
    gx = g x x∈

    gy : ℝ
    gy = g y y∈

    gx∈ : gx ∈ P
    gx∈ = g∈P x x∈

    gy∈ : gy ∈ P
    gy∈ = g∈P y y∈

    d : ℝ
    d = f' gx gx∈

    d＃ : 0 ＃ d
    d＃ = f'＃ gx gx∈

    d⁻¹ : ℝ
    d⁻¹ = invℝ d d＃

    forwardLower :
      rat (fst m) ·ᵣ absᵣ (gy -ᵣ gx) ≤ᵣ absᵣ (y -ᵣ x)
    forwardLower =
      isTrans≤≡ᵣ _ _ _
        (lower gy gy∈ gx gx∈)
        (cong absᵣ (cong₂ _-ᵣ_ (section y y∈) (section x x∈)))

    m·gy-gx≤m·δ :
      rat (fst m) ·ᵣ absᵣ (gy -ᵣ gx) ≤ᵣ
      rat (fst m) ·ᵣ rat (fst δ)
    m·gy-gx≤m·δ =
      isTrans≤≡ᵣ _ _ _
        (isTrans≤ᵣ _ _ _ forwardLower y-x≤mδ)
        (rat-·₊ m δ)

    gy-gx≤δ : absᵣ (gy -ᵣ gx) ≤ᵣ rat (fst δ)
    gy-gx≤δ =
      invEq
        (z≤x≃y₊·z≤y₊·x
          (rat (fst δ)) (absᵣ (gy -ᵣ gx)) (ℚ₊→ℝ₊ m))
        m·gy-gx≤m·δ

    E : ℝ
    E = derivativeErrorℙ P f f' gx gx∈ gy gy∈

    inverseErrorPath :
      derivativeErrorℙ Q g
        (λ u u∈ → invℝ (f' (g u u∈) (g∈P u u∈)) (f'＃ _ _))
        x x∈ y y∈
      ≡ -ᵣ d⁻¹ ·ᵣ E
    inverseErrorPath =
      cong (λ Δ → gy -ᵣ gx -ᵣ d⁻¹ ·ᵣ Δ)
        (cong₂ _-ᵣ_ (sym (section y y∈)) (sym (section x x∈)))
      ∙ ℝ!
      ∙ cong (λ t → (-ᵣ d⁻¹ ·ᵣ (f gy gy∈ -ᵣ f gx gx∈))
                       +ᵣ t ·ᵣ (gy -ᵣ gx))
          (sym (x·invℝ[x] d d＃))
      ∙ ℝ!

    errorAbsPath :
      absᵣ (derivativeErrorℙ Q g
        (λ u u∈ → invℝ (f' (g u u∈) (g∈P u u∈)) (f'＃ _ _))
        x x∈ y y∈)
      ≡ absᵣ d⁻¹ ·ᵣ absᵣ E
    errorAbsPath =
      cong absᵣ inverseErrorPath
      ∙ ·absᵣ (-ᵣ d⁻¹) E
      ∙ cong (_·ᵣ absᵣ E) (sym (-absᵣ d⁻¹))

    denominator·q≤εm : fst denominator ·ᵣ rat q ≤ᵣ fst εm
    denominator·q≤εm =
      <ᵣWeaken≤ᵣ _ _
        (fst (z<x/y₊≃y₊·z<x (fst εm) (rat q) denominator)
          q<ηBound)

    coefficient≤ :
      absᵣ d⁻¹ ·ᵣ rat q ≤ᵣ rat (fst ε) ·ᵣ rat (fst m)
    coefficient≤ =
      isTrans≤≡ᵣ _ _ _
        (isTrans≤ᵣ _ _ _
          (≤ᵣ-·ᵣo (absᵣ d⁻¹) (fst denominator) (rat q)
            (<ᵣWeaken≤ᵣ _ _ 0<q)
            (isTrans≤ᵣ _ _ _ (invBound gx gx∈) ratM≤denominator))
          denominator·q≤εm)
        refl

  chooseEta :
    Σ[ q ∈ ℚ ] (0 <ᵣ rat q) × (rat q <ᵣ fst ηBound) →
    ∃[ δ ∈ ℚ₊ ]
      (∀ x x∈ y y∈ → absᵣ (y -ᵣ x) ≤ᵣ rat (fst δ) →
        absᵣ (derivativeErrorℙ Q g
          (λ u u∈ → invℝ (f' (g u u∈) (g∈P u u∈)) (f'＃ _ _))
          x x∈ y y∈)
        ≤ᵣ rat (fst ε) ·ᵣ absᵣ (y -ᵣ x))
  chooseEta (q , 0<q , q<ηBound) =
    PT.map
      (λ (δ , D) →
        m ·₊ δ , λ x x∈ y y∈ y-x≤mδ →
          estimate q 0<q q<ηBound δ D x x∈ y y∈ y-x≤mδ)
      (df (q , <ᵣ→<ℚ 0 q 0<q))
