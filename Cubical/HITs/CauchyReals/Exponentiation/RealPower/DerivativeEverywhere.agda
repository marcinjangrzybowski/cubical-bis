module Cubical.HITs.CauchyReals.Exponentiation.RealPower.DerivativeEverywhere where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat as ℕ hiding (_+_; _·_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (ℤ)
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Exponentiation.Base
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Construction
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Derivative

module BDLDerivativeEverywhere
  (z : ℝ₊) (Z : ℕ)
  (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
  (1/Z≤z : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z)
  where

  open BDL z Z z≤Z 1/Z≤z
  open BDLDerivative z Z z≤Z 1/Z≤z

  private
    opaque
      𝒇-shift : ∀ x y → 𝒇 y ≡ 𝒇 x ·ᵣ 𝒇 (y -ᵣ x)
      𝒇-shift x y =
        cong 𝒇 (sym (+ᵣComm x (y -ᵣ x) ∙ Rℝ.minusPlus y x))
        ∙ sym (𝒇· x (y -ᵣ x))

    opaque
      𝒇-zeroFactor : ∀ x → 𝒇 x ≡ 𝒇 x ·ᵣ 𝒇 0
      𝒇-zeroFactor x =
        sym (·IdR (𝒇 x)) ∙ cong (𝒇 x ·ᵣ_) (sym 𝒇-zero-real)

    opaque
      𝒇-errorTranslate : ∀ x y →
        𝒇 y -ᵣ 𝒇 x -ᵣ (𝒇 x ·ᵣ preLn) ·ᵣ (y -ᵣ x) ≡
        𝒇 x ·ᵣ (𝒇 (y -ᵣ x) -ᵣ 𝒇 0 -ᵣ preLn ·ᵣ (y -ᵣ x))
      𝒇-errorTranslate x y =
        cong₂ _-ᵣ_
          (cong₂ _-ᵣ_ (𝒇-shift x y) (𝒇-zeroFactor x))
          refl
        ∙ cong₂ _-ᵣ_
            (sym (Rℝ.·DistR- (𝒇 x) (𝒇 (y -ᵣ x)) (𝒇 0)))
            (sym (·ᵣAssoc (𝒇 x) preLn (y -ᵣ x)))
        ∙ sym (Rℝ.·DistR- (𝒇 x)
            (𝒇 (y -ᵣ x) -ᵣ 𝒇 0) (preLn ·ᵣ (y -ᵣ x)))

  𝒇-derivative :
    DerivativeOfℙ ⊤Pred , (λ x _ → 𝒇 x) is
      (λ x _ → 𝒇 x ·ᵣ preLn)
  𝒇-derivative x x∈ ε =
    PT.rec squash₁ chooseTolerance
      (denseℚinℝ 0 (fst toleranceBound) (snd toleranceBound))
    where
    coefficient : ℝ
    coefficient = 𝒇 x

    denominator : ℝ₊
    denominator =
      absᵣ coefficient +ᵣ 1 ,
        isTrans≡<ᵣ _ _ _ (sym (+ᵣ-rat _ _))
          (≤<ᵣMonotone+ᵣ 0 (absᵣ coefficient) 0 1
            (0≤absᵣ coefficient) (decℚ<ᵣ? {0} {1}))

    toleranceBound : ℝ₊
    toleranceBound = ℚ₊→ℝ₊ ε ₊·ᵣ invℝ₊ denominator

    coefficient≤denominator : absᵣ coefficient ≤ᵣ fst denominator
    coefficient≤denominator =
      isTrans≡≤ᵣ _ _ _ (sym (+IdR (absᵣ coefficient)))
        (≤ᵣ-o+ 0 1 (absᵣ coefficient) decℚ≤ᵣ?)

    opaque
      estimate :
        (q : ℚ) → 0 <ᵣ rat q → rat q <ᵣ fst toleranceBound →
        (δ : ℚ₊) →
        (∀ r → absᵣ r ≤ᵣ rat (fst δ) →
          absᵣ (𝒇 r -ᵣ 𝒇 0 -ᵣ preLn ·ᵣ r) ≤ᵣ
            rat q ·ᵣ absᵣ r) →
        ∀ y y∈ → absᵣ (y -ᵣ x) ≤ᵣ rat (fst δ) →
          absᵣ (derivativeErrorℙ ⊤Pred
            (λ u _ → 𝒇 u) (λ u _ → 𝒇 u ·ᵣ preLn)
            x x∈ y y∈) ≤ᵣ
          rat (fst ε) ·ᵣ absᵣ (y -ᵣ x)
      estimate q 0<q q<tolerance δ D y y∈ y-x≤δ =
        isTrans≡≤ᵣ _ _ _
          (cong absᵣ (𝒇-errorTranslate x y)
           ∙ ·absᵣ coefficient
               (𝒇 (y -ᵣ x) -ᵣ 𝒇 0 -ᵣ preLn ·ᵣ (y -ᵣ x)))
          (isTrans≤ᵣ _ _ _
            (≤ᵣ-o·ᵣ _ _ (absᵣ coefficient) (0≤absᵣ coefficient)
              (D (y -ᵣ x) y-x≤δ))
            (isTrans≡≤ᵣ _ _ _
              (·ᵣAssoc (absᵣ coefficient) (rat q) (absᵣ (y -ᵣ x)))
              (≤ᵣ-·ᵣo
                (absᵣ coefficient ·ᵣ rat q)
                (rat (fst ε))
                (absᵣ (y -ᵣ x))
                (0≤absᵣ (y -ᵣ x))
                coefficientBound)))
        where
        denominator·q≤ε : fst denominator ·ᵣ rat q ≤ᵣ rat (fst ε)
        denominator·q≤ε =
          <ᵣWeaken≤ᵣ _ _
            (fst (z<x/y₊≃y₊·z<x
              (rat (fst ε)) (rat q) denominator) q<tolerance)

        coefficientBound :
          absᵣ coefficient ·ᵣ rat q ≤ᵣ rat (fst ε)
        coefficientBound =
          isTrans≤ᵣ _ _ _
            (≤ᵣ-·ᵣo (absᵣ coefficient) (fst denominator) (rat q)
              (<ᵣWeaken≤ᵣ _ _ 0<q) coefficient≤denominator)
            denominator·q≤ε

      chooseTolerance :
        Σ[ q ∈ ℚ ] (0 <ᵣ rat q) × (rat q <ᵣ fst toleranceBound) →
        ∃[ δ ∈ ℚ₊ ]
          (∀ y (y∈ : y ∈ ⊤Pred) →
            absᵣ (y -ᵣ x) ≤ᵣ rat (fst δ) →
            absᵣ (derivativeErrorℙ ⊤Pred
              (λ u _ → 𝒇 u) (λ u _ → 𝒇 u ·ᵣ preLn)
              x x∈ y y∈) ≤ᵣ
            rat (fst ε) ·ᵣ absᵣ (y -ᵣ x))
      chooseTolerance (q , 0<q , q<tolerance) =
        PT.map
          (λ (δ , D) →
            δ , λ y y∈ y-x≤δ →
              estimate q 0<q q<tolerance δ D y y∈ y-x≤δ)
          (𝒇-derivativeAtZero (q , <ᵣ→<ℚ 0 q 0<q))
