module Cubical.HITs.CauchyReals.Calculus.Derivative.Scaling where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Algebra.Order.Archimedean using
  (∃ℚ₊LargerThanℝ₀₊)
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

scaleInputDerivative : ∀ C (f f' : ℝ → ℝ) →
  DerivativeOfℙ ⊤Pred , (λ x _ → f x) is (λ x _ → f' x) →
  DerivativeOfℙ ⊤Pred , (λ x _ → f (C ·ᵣ x)) is
    (λ x _ → f' (C ·ᵣ x) ·ᵣ C)
scaleInputDerivative C f f' df =
  PT.rec
    (isProp-DerivativeOfℙ ⊤Pred
      (λ x _ → f (C ·ᵣ x))
      (λ x _ → f' (C ·ᵣ x) ·ᵣ C))
    withBound
    (∃ℚ₊LargerThanℝ₀₊ (absᵣ C , 0≤absᵣ C))
  where
  withBound :
    Σ[ M ∈ ℚ₊ ] absᵣ C <ᵣ rat (fst M) →
    DerivativeOfℙ ⊤Pred , (λ x _ → f (C ·ᵣ x)) is
      (λ x _ → f' (C ·ᵣ x) ·ᵣ C)
  withBound (M , absC<M) x _ ε =
    PT.map transformModulus (df (C ·ᵣ x) tt η)
    where
    η : ℚ₊
    η = invℚ₊ M ·₊ ε

    absC≤M : absᵣ C ≤ᵣ rat (fst M)
    absC≤M = <ᵣWeaken≤ᵣ _ _ absC<M

    η·M≡ε : rat (fst η) ·ᵣ rat (fst M) ≡ rat (fst ε)
    η·M≡ε =
      ·ᵣComm _ _
      ∙ sym (rat·ᵣrat (fst M) (fst η))
      ∙ cong rat (ℚ.y·[x/y] M (fst ε))

    transformModulus :
      Σ[ δ ∈ ℚ₊ ]
        (∀ y y∈ → absᵣ (y -ᵣ C ·ᵣ x) ≤ᵣ rat (fst δ) →
          absᵣ (derivativeErrorℙ ⊤Pred
            (λ u _ → f u) (λ u _ → f' u)
            (C ·ᵣ x) tt y y∈) ≤ᵣ
          rat (fst η) ·ᵣ absᵣ (y -ᵣ C ·ᵣ x)) →
      Σ[ δ' ∈ ℚ₊ ]
        (∀ y y∈ → absᵣ (y -ᵣ x) ≤ᵣ rat (fst δ') →
          absᵣ (derivativeErrorℙ ⊤Pred
            (λ u _ → f (C ·ᵣ u))
            (λ u _ → f' (C ·ᵣ u) ·ᵣ C)
            x tt y y∈) ≤ᵣ
          rat (fst ε) ·ᵣ absᵣ (y -ᵣ x))
    transformModulus (δ , D) =
      δScaled , λ y _ y-x≤δScaled →
        isTrans≡≤ᵣ _ _ _
          (cong absᵣ (scaledErrorPath y))
          (isTrans≤ᵣ _ _ _
            (D (C ·ᵣ y) tt (scaledDistance≤δ y y-x≤δScaled))
            (remainderCoefficient≤ y))
      where
      δScaled : ℚ₊
      δScaled = invℚ₊ M ·₊ δ

      M·δScaled≡δ :
        rat (fst M) ·ᵣ rat (fst δScaled) ≡ rat (fst δ)
      M·δScaled≡δ =
        sym (rat·ᵣrat (fst M) (fst δScaled))
        ∙ cong rat (ℚ.y·[x/y] M (fst δ))

      scaledDistancePath : ∀ y →
        absᵣ (C ·ᵣ y -ᵣ C ·ᵣ x) ≡
          absᵣ C ·ᵣ absᵣ (y -ᵣ x)
      scaledDistancePath y =
        cong absᵣ (sym (Rℝ.·DistR- C y x))
        ∙ ·absᵣ C (y -ᵣ x)

      scaledDistance≤δ : ∀ y →
        absᵣ (y -ᵣ x) ≤ᵣ rat (fst δScaled) →
        absᵣ (C ·ᵣ y -ᵣ C ·ᵣ x) ≤ᵣ rat (fst δ)
      scaledDistance≤δ y y-x≤δScaled =
        isTrans≡≤ᵣ _ _ _ (scaledDistancePath y)
          (isTrans≤≡ᵣ _ _ _
            (≤ᵣ₊Monotone·ᵣ
              (absᵣ C) (rat (fst M))
              (absᵣ (y -ᵣ x)) (rat (fst δScaled))
              (<ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ M)))
              (0≤absᵣ (y -ᵣ x))
              absC≤M y-x≤δScaled)
            M·δScaled≡δ)

      scaledErrorPath : ∀ y →
        derivativeErrorℙ ⊤Pred
          (λ u _ → f (C ·ᵣ u))
          (λ u _ → f' (C ·ᵣ u) ·ᵣ C)
          x tt y tt
        ≡ derivativeErrorℙ ⊤Pred
          (λ u _ → f u) (λ u _ → f' u)
          (C ·ᵣ x) tt (C ·ᵣ y) tt
      scaledErrorPath y = ℝ!

      coefficient≤ :
        rat (fst η) ·ᵣ absᵣ C ≤ᵣ rat (fst ε)
      coefficient≤ =
        isTrans≤≡ᵣ _ _ _
          (≤ᵣ-o·ᵣ (absᵣ C) (rat (fst M)) (rat (fst η))
            (<ᵣWeaken≤ᵣ _ _ (snd (ℚ₊→ℝ₊ η))) absC≤M)
          η·M≡ε

      remainderCoefficient≤ : ∀ y →
        rat (fst η) ·ᵣ absᵣ (C ·ᵣ y -ᵣ C ·ᵣ x) ≤ᵣ
          rat (fst ε) ·ᵣ absᵣ (y -ᵣ x)
      remainderCoefficient≤ y =
        isTrans≡≤ᵣ _ _ _
          (cong (rat (fst η) ·ᵣ_) (scaledDistancePath y)
           ∙ ·ᵣAssoc (rat (fst η)) (absᵣ C) (absᵣ (y -ᵣ x)))
          (≤ᵣ-·ᵣo _ _ (absᵣ (y -ᵣ x))
            (0≤absᵣ (y -ᵣ x)) coefficient≤)
