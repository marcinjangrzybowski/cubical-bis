module Cubical.HITs.CauchyReals.Exponentiation.RealPowerDerivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat as ℕ hiding (_+_; _·_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (ℤ)
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.ContinuousApart
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)
open import Cubical.HITs.CauchyReals.Derivative hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Exponentiation
open import Cubical.HITs.CauchyReals.Exponentiation.LogSequenceElementary
  using (lnSeq; lnSeq'; seqΔ-δ; stepℚ₊)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower

open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

module BDLDerivative
  (z : ℝ₊) (Z : ℕ)
  (z≤Z : fst z ≤ᵣ fromNat (suc (suc Z)))
  (1/Z≤z : rat [ 1 / fromNat (suc (suc Z)) ] ≤ᵣ fst z)
  where

  open BDL z Z z≤Z 1/Z≤z

  private
    slopeEstimateAtZero : ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
      (∀ r 0＃r → absᵣ (0 -ᵣ r) <ᵣ rat (fst δ) →
        absᵣ (preLn -ᵣ 𝒇-diffQuot r 0＃r) <ᵣ rat (fst ε))
    slopeEstimateAtZero ε =
      let
        N = fst (seqΔ-δ Z ε)
        width = stepℚ₊ (suc N)
      in
      width , λ r 0＃r ∣r∣<width →
        let
          r≤width : r ≤ᵣ rat (fst width)
          r≤width =
            isTrans≤ᵣ _ _ _ (≤absᵣ r)
              (isTrans≡≤ᵣ _ _ _
                (cong absᵣ (sym (Rℝ.+IdR' _ _ (-ᵣ-rat 0)))
                 ∙ minusComm-absᵣ _ _)
                (<ᵣWeaken≤ᵣ _ _ ∣r∣<width))

          -width≤r : rat (ℚ.- fst width) ≤ᵣ r
          -width≤r =
            isTrans≤ᵣ _ _ _
              (isTrans≡≤ᵣ _ _ _
                (sym (-ᵣ-rat (fst width)))
                (-ᵣ≤ᵣ _ _ (<ᵣWeaken≤ᵣ _ _ ∣r∣<width)))
              (≤ᵣ-ᵣ _ _
                (isTrans≤≡ᵣ _ _ _ (≤absᵣ (-ᵣ r))
                  (cong absᵣ (sym (+IdL _)) ∙ sym (-ᵣInvol _))))

          quotient∈ :
            𝒇-diffQuot r 0＃r ∈
              intervalℙ (lnSeq' z (suc N)) (lnSeq z (suc N))
          quotient∈ =
            lnSeq'≤𝒇-diffQuot (suc N) r 0＃r -width≤r ,
            𝒇-diffQuot≤lnSeq (suc N) r 0＃r r≤width
        in
        isTrans≤<ᵣ _ _ _
          (intervalℙ→dist< _ _ _ _
            (lnSeq'≤preLn (suc N) , preLn≤lnSeq (suc N))
            quotient∈)
          (seqΔ ε (suc N) ℕ.≤-refl)

    slopeLimitAtZero : at 0 limitOf 𝒇-diffQuot is preLn
    slopeLimitAtZero ε =
      PT.rec squash₁
        (λ (ε' , 0<ε' , ε'<ε) →
          let
            ε'₊ = ε' , <ᵣ→<ℚ 0 ε' 0<ε'
            estimate = slopeEstimateAtZero ε'₊
          in
          ∣ (ℚ₊→ℝ₊ (fst estimate) , λ r 0＃r ∣r∣<width →
              isTrans<ᵣ _ _ _
                (snd estimate r 0＃r ∣r∣<width) ε'<ε) ∣₁)
        (denseℚinℝ 0 (fst ε) (snd ε))

    opaque
      unfolding 𝒇-diffQuot

      quotientRemainder : ∀ r (0＃r : 0 ＃ r) →
        𝒇 r -ᵣ 𝒇 0 -ᵣ preLn ·ᵣ r ≡
        (𝒇-diffQuot r 0＃r -ᵣ preLn) ·ᵣ r
      quotientRemainder r 0＃r =
        cong (_-ᵣ preLn ·ᵣ r)
          (sym ([x/y]·yᵣ (𝒇 r -ᵣ 𝒇 0) r 0＃r))
        ∙ sym (Rℝ.·DistL- (𝒇-diffQuot r 0＃r) preLn r)

    𝒇-errorAtZero : ℝ → ℝ
    𝒇-errorAtZero r = 𝒇 r -ᵣ 𝒇 0 -ᵣ preLn ·ᵣ r

    𝒇-errorAtZero-cont : IsContinuous 𝒇-errorAtZero
    𝒇-errorAtZero-cont =
      cont₂+ᵣ _ _
        (IsContinuous∘ _ _ (IsContinuous+ᵣR (-ᵣ 𝒇 0)) 𝒇-cont)
        (IsContinuous∘ _ _ IsContinuous-ᵣ (IsContinuous·ᵣL preLn))

    𝒇-errorAtZero-zero : 𝒇-errorAtZero 0 ≡ 0
    𝒇-errorAtZero-zero =
      cong₂ _-ᵣ_ (+-ᵣ (𝒇 0)) (Rℝ.0RightAnnihilates preLn)
      ∙ +-ᵣ 0

    opaque
      𝒇-remainderEstimate : ∀ (ε : ℚ₊) r (0＃r : 0 ＃ r) →
        absᵣ (preLn -ᵣ 𝒇-diffQuot r 0＃r) <ᵣ rat (fst ε) →
        absᵣ (𝒇-errorAtZero r) ≤ᵣ rat (fst ε) ·ᵣ absᵣ r
      𝒇-remainderEstimate ε r 0＃r slopeBound =
        isTrans≡≤ᵣ _ _ _
          (cong absᵣ (quotientRemainder r 0＃r)
           ∙ ·absᵣ (𝒇-diffQuot r 0＃r -ᵣ preLn) r
           ∙ cong (_·ᵣ absᵣ r)
               (minusComm-absᵣ (𝒇-diffQuot r 0＃r) preLn))
          (≤ᵣ-·ᵣo _ _ (absᵣ r) (0≤absᵣ r)
            (<ᵣWeaken≤ᵣ _ _ slopeBound))

    symmetricClamp : ℚ₊ → ℝ → ℝ
    symmetricClamp δ = clampᵣ (-ᵣ rat (fst δ)) (rat (fst δ))

    symmetricClamp-cont : ∀ δ → IsContinuous (symmetricClamp δ)
    symmetricClamp-cont δ =
      IsContinuousClamp (-ᵣ rat (fst δ)) (rat (fst δ))

    opaque
      symmetricClamp-half-within-real : ∀ width r →
        absᵣ (0 -ᵣ symmetricClamp (width /2₊) r) <ᵣ rat (fst width)
      symmetricClamp-half-within-real width r =
        isTrans≡<ᵣ _ _ _
          (minusComm-absᵣ 0 clp
           ∙ cong absᵣ (Rℝ.+IdR' _ _ (-ᵣ-rat 0)))
          (isTrans≤<ᵣ _ _ _ absClp≤δ
            (<ℚ→<ᵣ _ _ (/2₊<id width)))
        where
        δ : ℚ₊
        δ = width /2₊

        δᵣ : ℝ
        δᵣ = rat (fst δ)

        clp : ℝ
        clp = symmetricClamp δ r

        -δ<δ : -ᵣ δᵣ <ᵣ δᵣ
        -δ<δ =
          isTrans<ᵣ _ _ _
            (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ 0 δᵣ (snd (ℚ₊→ℝ₊ δ)))
              (-ᵣ-rat 0))
            (snd (ℚ₊→ℝ₊ δ))

        lower≤clp : -ᵣ δᵣ ≤ᵣ clp
        lower≤clp = ≤clampᵣ (-ᵣ δᵣ) δᵣ r (<ᵣWeaken≤ᵣ _ _ -δ<δ)

        clp≤δ : clp ≤ᵣ δᵣ
        clp≤δ = clamp≤ᵣ (-ᵣ δᵣ) δᵣ r

        -clp≤δ : -ᵣ clp ≤ᵣ δᵣ
        -clp≤δ =
          isTrans≤≡ᵣ _ _ _ (-ᵣ≤ᵣ (-ᵣ δᵣ) clp lower≤clp)
            (-ᵣInvol δᵣ)

        absClp≤δ : absᵣ clp ≤ᵣ δᵣ
        absClp≤δ =
          isTrans≡≤ᵣ _ _ _ (abs-max clp)
            (max≤-lem clp (-ᵣ clp) δᵣ clp≤δ -clp≤δ)

      symmetricClamp-apart : ∀ δ r → 0 ＃ r →
        0 ＃ symmetricClamp δ r
      symmetricClamp-apart δ r =
        ⊎.map positiveCase negativeCase
        where
        δᵣ : ℝ
        δᵣ = rat (fst δ)

        positiveCase : 0 <ᵣ r → 0 <ᵣ symmetricClamp δ r
        positiveCase 0<r =
          <min-lem (maxᵣ (-ᵣ δᵣ) r) δᵣ 0
            (isTrans<≤ᵣ _ _ _ 0<r
              (isTrans≤≡ᵣ _ _ _ (≤maxᵣ r (-ᵣ δᵣ))
                (maxᵣComm r (-ᵣ δᵣ))))
            (snd (ℚ₊→ℝ₊ δ))

        negativeCase : r <ᵣ 0 → symmetricClamp δ r <ᵣ 0
        negativeCase r<0 =
          isTrans≤<ᵣ _ _ _
            (min≤ᵣ (maxᵣ (-ᵣ δᵣ) r) δᵣ)
            (max<-lem (-ᵣ δᵣ) r 0
              (isTrans<≡ᵣ _ _ _
                (-ᵣ<ᵣ 0 δᵣ (snd (ℚ₊→ℝ₊ δ))) (-ᵣ-rat 0))
              r<0)

      symmetricClamp-zeroEstimate : ∀ (ε δ : ℚ₊) →
        absᵣ (𝒇-errorAtZero (symmetricClamp δ 0)) ≤ᵣ
        rat (fst ε) ·ᵣ absᵣ (symmetricClamp δ 0)
      symmetricClamp-zeroEstimate ε δ =
        isTrans≡≤ᵣ _ _ _
          (cong absᵣ
            (cong 𝒇-errorAtZero clp≡0 ∙ 𝒇-errorAtZero-zero)
           ∙ absᵣ0)
          (0≤ε·abs ε (symmetricClamp δ 0))
        where
        δᵣ : ℝ
        δᵣ = rat (fst δ)

        0≤δᵣ : 0 ≤ᵣ δᵣ
        0≤δᵣ = <ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ δ))

        -δᵣ≤0 : -ᵣ δᵣ ≤ᵣ 0
        -δᵣ≤0 =
          isTrans≤≡ᵣ _ _ _ (-ᵣ≤ᵣ 0 δᵣ 0≤δᵣ) (-ᵣ-rat 0)

        clp≡0 : symmetricClamp δ 0 ≡ 0
        clp≡0 =
          sym (∈ℚintervalℙ→clampᵣ≡ (-ᵣ δᵣ) δᵣ 0
            (-δᵣ≤0 , 0≤δᵣ))

    𝒇-derivativeAtZeroImpl : ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
      (∀ r → absᵣ r ≤ᵣ rat (fst δ) →
        absᵣ (𝒇 r -ᵣ 𝒇 0 -ᵣ preLn ·ᵣ r) ≤ᵣ
        rat (fst ε) ·ᵣ absᵣ r)
    𝒇-derivativeAtZeroImpl ε =
      ∣ (δ , λ r ∣r∣≤δ →
        let
          r∈ : r ∈ intervalℙ (-ᵣ δᵣ) δᵣ
          r∈ =
            isTrans≤≡ᵣ _ _ _
              (-ᵣ≤ᵣ _ _
                (isTrans≤ᵣ _ _ _
                  (isTrans≤≡ᵣ _ _ _ (≤absᵣ (-ᵣ r)) (sym (-absᵣ r)))
                  ∣r∣≤δ))
              (-ᵣInvol r) ,
            isTrans≤ᵣ _ _ _ (≤absᵣ r) ∣r∣≤δ

          r≡clp : r ≡ clp r
          r≡clp = ∈ℚintervalℙ→clampᵣ≡ (-ᵣ δᵣ) δᵣ r r∈
        in
        subst2 _≤ᵣ_
          (cong absᵣ (cong 𝒇-errorAtZero (sym r≡clp)))
          (cong (rat (fst ε) ·ᵣ_) (cong absᵣ (sym r≡clp)))
          (clampedEstimate r)) ∣₁
      where
      estimate = slopeEstimateAtZero ε
      width : ℚ₊
      width = fst estimate

      δ : ℚ₊
      δ = width /2₊

      δᵣ : ℝ
      δᵣ = rat (fst δ)

      clp : ℝ → ℝ
      clp = symmetricClamp δ

      clpCont : IsContinuous clp
      clpCont = symmetricClamp-cont δ

      clampedEstimate : ∀ r →
        absᵣ (𝒇-errorAtZero (clp r)) ≤ᵣ
        rat (fst ε) ·ᵣ absᵣ (clp r)
      clampedEstimate =
        ≤ContinuousAwayFromZero
          (IsContinuous∘ _ _ IsContinuousAbsᵣ
            (IsContinuous∘ _ _ 𝒇-errorAtZero-cont clpCont))
          (IsContinuous∘ _ _ (IsContinuous·ᵣL (rat (fst ε)))
            (IsContinuous∘ _ _ IsContinuousAbsᵣ clpCont))
          (symmetricClamp-zeroEstimate ε δ)
          awayFromZero
        where
        awayFromZero : ∀ r → 0 ＃ r →
          absᵣ (𝒇-errorAtZero (clp r)) ≤ᵣ
          rat (fst ε) ·ᵣ absᵣ (clp r)
        awayFromZero r 0＃r =
          𝒇-remainderEstimate ε (clp r) clpApart
            (snd estimate (clp r) clpApart
              (symmetricClamp-half-within-real width r))
          where
          clpApart : 0 ＃ clp r
          clpApart = symmetricClamp-apart δ r 0＃r

  𝒇-derivativeAtZero : ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
    (∀ r → absᵣ r ≤ᵣ rat (fst δ) →
      absᵣ (𝒇 r -ᵣ 𝒇 0 -ᵣ preLn ·ᵣ r) ≤ᵣ
      rat (fst ε) ·ᵣ absᵣ r)
  𝒇-derivativeAtZero = 𝒇-derivativeAtZeroImpl
