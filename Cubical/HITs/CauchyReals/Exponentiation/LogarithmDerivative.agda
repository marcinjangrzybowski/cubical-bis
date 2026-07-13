module Cubical.HITs.CauchyReals.Exponentiation.LogarithmDerivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Equiv using (invEq)

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.OrderBounds
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)
open import Cubical.HITs.CauchyReals.Derivative hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.ExponentiationMore using (ln; ln-cont)
open import Cubical.HITs.CauchyReals.Exponentiation.LogarithmDerivativeBounded

private
  oneℚ₊ : ℚ₊
  oneℚ₊ = 1

  oneℝ : ℝ
  oneℝ = rat (fst oneℚ₊)

  logBoundTarget : ∀ x → 0 <ᵣ x → ℝ₀₊
  logBoundTarget x 0<x =
    absᵣ (ln (x , 0<x)) +ᵣ oneℝ
    , isTrans≡≤ᵣ _ _ _
        (sym (+ᵣ-rat 0 0))
        (≤ᵣMonotone+ᵣ 0 (absᵣ (ln (x , 0<x))) 0 oneℝ
          (0≤absᵣ (ln (x , 0<x)))
          (<ᵣWeaken≤ᵣ 0 oneℝ (snd (ℚ₊→ℝ₊ oneℚ₊))))

  centerInBoundedLog : ∀ x (0<x : 0 <ᵣ x) B →
    fst (logBoundTarget x 0<x) <ᵣ rat (fst B) →
    x ∈ boundedLogPred B
  centerInBoundedLog x 0<x B target<B =
    0<x
    , subst
        (λ lower → lnX ∈ intervalℙ lower (rat (fst B)))
        (-ᵣ-rat (fst B))
        (abs≤→interval lnX (rat (fst B))
          (<ᵣWeaken≤ᵣ _ _ absLnX<B))
    where
    lnX : ℝ
    lnX = ln (x , 0<x)

    absLnX<target : absᵣ lnX <ᵣ fst (logBoundTarget x 0<x)
    absLnX<target =
      isTrans≡<ᵣ _ _ _ (sym (+IdR (absᵣ lnX)))
        (<ᵣ-o+ 0 oneℝ (absᵣ lnX) (snd (ℚ₊→ℝ₊ oneℚ₊)))

    absLnX<B : absᵣ lnX <ᵣ rat (fst B)
    absLnX<B = isTrans<ᵣ _ _ _ absLnX<target target<B

  nearbyInBoundedLog : ∀ x (0<x : 0 <ᵣ x) B →
    fst (logBoundTarget x 0<x) <ᵣ rat (fst B) →
    (w : ℚ₊) →
    (∀ y (0<y : 0 <ᵣ y) → x ∼[ w ] y →
      ln (x , 0<x) ∼[ oneℚ₊ ] ln (y , 0<y)) →
    ∀ y (0<y : 0 <ᵣ y) →
      absᵣ (y -ᵣ x) ≤ᵣ rat (fst (w /2₊)) →
      y ∈ boundedLogPred B
  nearbyInBoundedLog x 0<x B target<B w logClose y 0<y y-x≤w/2 =
    0<y
    , subst
        (λ lower → lnY ∈ intervalℙ lower (rat (fst B)))
        (-ᵣ-rat (fst B))
        (abs≤→interval lnY (rat (fst B))
          (<ᵣWeaken≤ᵣ _ _ absLnY<B))
    where
    lnX lnY : ℝ
    lnX = ln (x , 0<x)
    lnY = ln (y , 0<y)

    y-x<w : absᵣ (y -ᵣ x) <ᵣ rat (fst w)
    y-x<w =
      isTrans≤<ᵣ _ _ _ y-x≤w/2
        (<ℚ→<ᵣ _ _ (/2₊<id w))

    x∼w : x ∼[ w ] y
    x∼w =
      invEq (∼≃abs<ε x y w)
        (isTrans≡<ᵣ _ _ _ (minusComm-absᵣ x y) y-x<w)

    lnX-lnY<one : absᵣ (lnX -ᵣ lnY) <ᵣ oneℝ
    lnX-lnY<one =
      fst (∼≃abs<ε lnX lnY oneℚ₊) (logClose y 0<y x∼w)

    lnY-lnX<one : absᵣ (lnY -ᵣ lnX) <ᵣ oneℝ
    lnY-lnX<one =
      isTrans≡<ᵣ _ _ _ (minusComm-absᵣ lnY lnX) lnX-lnY<one

    recombine : lnY ≡ (lnY -ᵣ lnX) +ᵣ lnX
    recombine = sym
      (sym (+ᵣAssoc lnY (-ᵣ lnX) lnX)
      ∙ cong (lnY +ᵣ_) (+ᵣComm (-ᵣ lnX) lnX ∙ +-ᵣ lnX)
      ∙ +IdR lnY)

    absLnY<target : absᵣ lnY <ᵣ fst (logBoundTarget x 0<x)
    absLnY<target =
      isTrans≤<ᵣ _ _ _
        (isTrans≡≤ᵣ _ _ _
          (cong absᵣ recombine)
          (absᵣ-triangle (lnY -ᵣ lnX) lnX))
        (isTrans<≡ᵣ _ _ _
          (<≤ᵣMonotone+ᵣ
            (absᵣ (lnY -ᵣ lnX)) oneℝ
            (absᵣ lnX) (absᵣ lnX)
            lnY-lnX<one (≤ᵣ-refl (absᵣ lnX)))
          (+ᵣComm oneℝ (absᵣ lnX)))

    absLnY<B : absᵣ lnY <ᵣ rat (fst B)
    absLnY<B = isTrans<ᵣ _ _ _ absLnY<target target<B

lnDerivativeValue : ∀ x → x ∈ pred0< → ℝ
lnDerivativeValue x 0<x = fst (invℝ₊ (x , 0<x))

opaque
  -- Previous name: ln-der, for the quotient-slope derivative.
  lnDerivative :
    DerivativeOfℙ pred0< , curry ln is lnDerivativeValue
  lnDerivative x 0<x ε = do
    (B , target<B) ← ∃ℚ₊LargerThanℝ₀₊ (logBoundTarget x 0<x)
    (w , logClose) ← ln-cont x oneℚ₊ 0<x
    let x∈B = centerInBoundedLog x 0<x B target<B
    (d , derivativeBound) ← boundedLogDerivative B x x∈B ε
    let
      δ = min₊ d (w /2₊)
      δ≤d : fst δ ℚ.≤ fst d
      δ≤d = ℚ.min≤ (fst d) (fst (w /2₊))
      δ≤w/2 : fst δ ℚ.≤ fst (w /2₊)
      δ≤w/2 = ℚ.min≤' (fst d) (fst (w /2₊))
    ∣ δ , (λ y 0<y y-x≤δ →
        let
          y-x≤d = isTrans≤ᵣ _ _ _ y-x≤δ (≤ℚ→≤ᵣ _ _ δ≤d)
          y-x≤w/2 = isTrans≤ᵣ _ _ _ y-x≤δ (≤ℚ→≤ᵣ _ _ δ≤w/2)
          y∈B = nearbyInBoundedLog x 0<x B target<B
            w logClose y 0<y y-x≤w/2
        in derivativeBound y y∈B y-x≤d) ∣₁
