module Cubical.HITs.CauchyReals.Exponentiation.RealPowerBounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset

open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.Exponentiation.RealPowerBase

powerExponentSlopeLowerConstant :
  (z : ℝ₊) → (B : ℚ₊) → 1 <ᵣ fst z → ℝ₊
powerExponentSlopeLowerConstant z B 1<z =
  (z ^ℚ (ℚ.- fst B)) ₊·ᵣ
  ((fst z -ᵣ 1 , x<y→0<y-x 1 (fst z) 1<z) ₊·ᵣ invℝ₊ z)

powerExponentDifferenceLower< :
  (z : ℝ₊) → (B : ℚ₊) → (1<z : 1 <ᵣ fst z) →
  (y₀ y₁ : ℚ) → (y₀<y₁ : y₀ ℚ.< y₁) →
  y₀ ∈ ℚ.ℚintervalℙ (ℚ.- fst B) (fst B) →
  y₁ ∈ ℚ.ℚintervalℙ (ℚ.- fst B) (fst B) →
  fst (powerExponentSlopeLowerConstant z B 1<z) ·ᵣ
    fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ y₀ y₁ y₀<y₁))
  ≤ᵣ
  fst (z ^ℚ y₁) -ᵣ fst (z ^ℚ y₀)
powerExponentDifferenceLower< z B 1<z y₀ y₁ y₀<y₁ y₀∈ y₁∈ =
  <ᵣWeaken≤ᵣ _ _
    (isTrans≡<ᵣ _ _ _
      (·ᵣComm _ _)
      (fst
        (z<x/y₊≃y₊·z<x
          (fst (z ^ℚ y₁) -ᵣ fst (z ^ℚ y₀))
          (fst (powerExponentSlopeLowerConstant z B 1<z))
          (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ y₀ y₁ y₀<y₁)))
        (slope-lower-bound z B 1<z y₀ y₁ y₀<y₁ y₀∈ y₁∈)))

powerExponentDifferenceLowerℚ :
  (z : ℝ₊) → (B : ℚ₊) → (1<z : 1 <ᵣ fst z) →
  (x y : ℚ) →
  x ∈ ℚ.ℚintervalℙ (ℚ.- fst B) (fst B) →
  y ∈ ℚ.ℚintervalℙ (ℚ.- fst B) (fst B) →
  fst (powerExponentSlopeLowerConstant z B 1<z) ·ᵣ
    rat (abs (y ℚ.- x))
  ≤ᵣ
  absᵣ (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x))
powerExponentDifferenceLowerℚ z B 1<z =
  ℚ.elimBy≡⊎<'
    (λ x y X y∈ x∈ →
      subst2 _≤ᵣ_
        (cong (fst (powerExponentSlopeLowerConstant z B 1<z) ·ᵣ_)
          (cong rat (abs-Comm y x)))
        (minusComm-absᵣ _ _)
        (X x∈ y∈))
    (λ x _ _ →
      isTrans≡≤ᵣ _ 0 _
        (cong (fst (powerExponentSlopeLowerConstant z B 1<z) ·ᵣ_)
            (cong rat (cong abs (ℚ.+InvR x)))
          ∙ Rℝ.0RightAnnihilates _)
        (0≤absᵣ _))
    λ x h₊ x∈ y∈ →
      let
        y = x ℚ.+ fst h₊
        x<y = subst (λ q → q ℚ.< y) (ℚ.+IdR x)
          (ℚ.≤<Monotone+ x x 0 (fst h₊)
            (ℚ.isRefl≤ x) (snd h₊))
      in
      isTrans≡≤ᵣ
        (fst (powerExponentSlopeLowerConstant z B 1<z) ·ᵣ
          rat (abs (y ℚ.- x)))
        (fst (powerExponentSlopeLowerConstant z B 1<z) ·ᵣ
          fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ x y x<y)))
        (absᵣ (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)))
        (cong (fst (powerExponentSlopeLowerConstant z B 1<z) ·ᵣ_)
          (cong rat
            (0<→abs≡id (y ℚ.- x) (ℚ.-< x y x<y))))
        (isTrans≤≡ᵣ
          (fst (powerExponentSlopeLowerConstant z B 1<z) ·ᵣ
            fst (ℚ₊→ℝ₊ (ℚ.<→ℚ₊ x y x<y)))
          (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x))
          (absᵣ (fst (z ^ℚ y) -ᵣ fst (z ^ℚ x)))
          (powerExponentDifferenceLower< z B 1<z x y x<y x∈ y∈)
          (sym
            (absᵣNonNeg _
              (x≤y→0≤y-x _ _
                (^ℚ-MonotoneR {z} x y (ℚ.<Weaken≤ x y x<y)
                  (<ᵣWeaken≤ᵣ 1 (fst z) 1<z))))))
