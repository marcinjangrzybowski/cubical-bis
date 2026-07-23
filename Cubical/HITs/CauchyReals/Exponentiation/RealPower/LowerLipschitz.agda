module Cubical.HITs.CauchyReals.Exponentiation.RealPower.LowerLipschitz where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base hiding (≤Cont₂)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Order using (≤Cont₂)
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Inverse
open import Cubical.HITs.CauchyReals.Exponentiation.Base
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Bounds
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition

private
  symmetricIntervalOrdered : (B : ℚ₊) → ℚ.- fst B ℚ.≤ fst B
  symmetricIntervalOrdered B =
    ℚ.isTrans≤ (ℚ.- fst B) 0 (fst B)
      (ℚ.<Weaken≤ _ _
        (subst ((ℚ.- fst B) ℚ.<_) ℚ!
          (ℚ.minus-< 0 (fst B) (snd B))))
      (ℚ.<Weaken≤ _ _ (snd B))

module _ (z : ℝ₊) (B : ℚ₊) (1<z : 1 <ᵣ fst z) where
  private
    slopeLower : ℝ₊
    slopeLower = powerExponentSlopeLowerConstant z B 1<z

    lowerEnd upperEnd : ℝ
    lowerEnd = rat (ℚ.- fst B)
    upperEnd = rat (fst B)

    lowerEnd≤upperEnd : lowerEnd ≤ᵣ upperEnd
    lowerEnd≤upperEnd = ≤ℚ→≤ᵣ _ _ (symmetricIntervalOrdered B)

    clp : ℝ → ℝ
    clp = clampᵣ lowerEnd upperEnd

    clpCont : IsContinuous clp
    clpCont = IsContinuousClamp lowerEnd upperEnd

    power : ℝ → ℝ
    power = fst ∘ z ^ᵣ_

    powerCont : IsContinuous power
    powerCont = cont-^ z

    opaque
      unfolding _+ᵣ_
      clampedDifferenceLower : ∀ u v →
        fst slopeLower ·ᵣ absᵣ (clp u -ᵣ clp v) ≤ᵣ
        absᵣ (power (clp u) -ᵣ power (clp v))
      clampedDifferenceLower =
       ≤Cont₂
        (cont∘₂
          (IsContinuous∘ _ _ (IsContinuous·ᵣL (fst slopeLower)) IsContinuousAbsᵣ)
          (cont₂∘ (contNE₂ sumR)
            clpCont (IsContinuous∘ _ _ IsContinuous-ᵣ clpCont)))
        (cont∘₂ IsContinuousAbsᵣ
          (cont₂∘ (contNE₂ sumR)
            (IsContinuous∘ _ _ powerCont clpCont)
            (IsContinuous∘ _ _ IsContinuous-ᵣ
              (IsContinuous∘ _ _ powerCont clpCont))))
        rationalCase
       where
       rationalCase : ∀ x y →
        fst slopeLower ·ᵣ absᵣ (clp (rat x) -ᵣ clp (rat y)) ≤ᵣ
        absᵣ (power (clp (rat x)) -ᵣ power (clp (rat y)))
       rationalCase x y =
        let
          x' = ℚ.clamp (ℚ.- fst B) (fst B) x
          y' = ℚ.clamp (ℚ.- fst B) (fst B) y
          x'∈ = ℚ.clam∈ℚintervalℙ (ℚ.- fst B) (fst B)
            (symmetricIntervalOrdered B) x
          y'∈ = ℚ.clam∈ℚintervalℙ (ℚ.- fst B) (fst B)
            (symmetricIntervalOrdered B) y
        in
        subst2 _≤ᵣ_
          (cong (fst slopeLower ·ᵣ_)
            (sym (absᵣ-rat (x' ℚ.- y'))
             ∙ cong absᵣ (sym (-ᵣ-rat₂ x' y'))
             ∙ cong absᵣ
                 (cong₂ _-ᵣ_
                   (sym (clampᵣ-rat (ℚ.- fst B) (fst B) x))
                   (sym (clampᵣ-rat (ℚ.- fst B) (fst B) y)))))
          (cong absᵣ
            (cong₂ _-ᵣ_
              (sym (^-rat z x')
               ∙ cong power
                   (sym (clampᵣ-rat (ℚ.- fst B) (fst B) x)))
              (sym (^-rat z y')
               ∙ cong power
                   (sym (clampᵣ-rat (ℚ.- fst B) (fst B) y)))))
          (powerExponentDifferenceLowerℚ z B 1<z y' x' y'∈ x'∈)

  powerExponentDifferenceLower : ∀ u v →
    u ∈ intervalℙ lowerEnd upperEnd →
    v ∈ intervalℙ lowerEnd upperEnd →
    fst slopeLower ·ᵣ absᵣ (u -ᵣ v) ≤ᵣ
    absᵣ (power u -ᵣ power v)
  powerExponentDifferenceLower u v u∈ v∈ =
    subst2 _≤ᵣ_
      (cong (fst slopeLower ·ᵣ_)
        (cong absᵣ
          (cong₂ _-ᵣ_
            (sym (∈ℚintervalℙ→clampᵣ≡ lowerEnd upperEnd u u∈))
            (sym (∈ℚintervalℙ→clampᵣ≡ lowerEnd upperEnd v v∈)))))
      (cong absᵣ
        (cong₂ _-ᵣ_
          (cong power
            (sym (∈ℚintervalℙ→clampᵣ≡ lowerEnd upperEnd u u∈)))
          (cong power
            (sym (∈ℚintervalℙ→clampᵣ≡ lowerEnd upperEnd v v∈)))))
      (clampedDifferenceLower u v)

  powerExponentLowerLipschitz :
    ∃[ m ∈ ℚ₊ ]
      LowerLipschitz-ℝ→ℝℙ m
        (intervalℙ lowerEnd upperEnd)
        (λ x _ → power x)
  powerExponentLowerLipschitz =
    PT.map
      (λ (q , 0<q , q<lower) →
        let m = q , <ᵣ→<ℚ 0 q 0<q
        in m , λ u u∈ v v∈ →
          isTrans≤ᵣ _ _ _
            (≤ᵣ-·ᵣo (rat q) (fst slopeLower) (absᵣ (u -ᵣ v))
              (0≤absᵣ (u -ᵣ v)) (<ᵣWeaken≤ᵣ _ _ q<lower))
            (powerExponentDifferenceLower u v u∈ v∈))
      (denseℚinℝ 0 (fst slopeLower) (snd slopeLower))
