module Cubical.HITs.CauchyReals.Exponentiation.Logarithm.DerivativeBounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels using (isPropΣ)
open import Cubical.Functions.FunExtEquiv using (funExt₂)

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Inverse using (LowerLipschitz-ℝ→ℝℙ)
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Inverse
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition using (ln)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.LowerLipschitz
open import Cubical.HITs.CauchyReals.Exponentiation.Normalized.Exponential
open import Cubical.HITs.CauchyReals.Exponentiation.ExpLog.Derivative

exponentInterval : ℚ₊ → ℙ ℝ
exponentInterval B = intervalℙ (rat (ℚ.- fst B)) (rat (fst B))

boundedLogPred : ℚ₊ → ℙ ℝ
boundedLogPred B y =
  ( (Σ (0 <ᵣ y) λ 0<y →
      ln (y , 0<y) ∈ exponentInterval B)
  , isPropΣ (isProp<ᵣ 0 y)
      (λ 0<y → ∈-isProp (exponentInterval B) (ln (y , 0<y)))
  )

boundedLn : ∀ B y → y ∈ boundedLogPred B → ℝ
boundedLn B y y∈ = ln (y , fst y∈)

boundedLnDerivativeValue : ∀ B y → y ∈ boundedLogPred B → ℝ
boundedLnDerivativeValue B y y∈ = fst (invℝ₊ (y , fst y∈))

opaque
  boundedLogDerivative : ∀ B →
    DerivativeOfℙ boundedLogPred B , boundedLn B is
      boundedLnDerivativeValue B
  boundedLogDerivative B =
    PT.rec
      (isProp-DerivativeOfℙ
        (boundedLogPred B) (boundedLn B) (boundedLnDerivativeValue B))
      derive
      (powerExponentLowerLipschitz eBase B one<eBase)
    where
    powerOnInterval : ∀ x → x ∈ exponentInterval B → ℝ
    powerOnInterval x _ = fst (realExp x)

    powerDerivativeValue : ∀ x → x ∈ exponentInterval B → ℝ
    powerDerivativeValue x _ = fst (realExp x)

    powerDerivative :
      DerivativeOfℙ exponentInterval B , powerOnInterval is
        powerDerivativeValue
    powerDerivative =
      DerivativeOfℙ-restr
        ⊤Pred (exponentInterval B)
        (λ x _ → fst (realExp x))
        (λ x _ → fst (realExp x))
        (λ _ _ → tt)
        realExpDerivative

    powerDerivativeApart : ∀ x x∈ → 0 ＃ powerDerivativeValue x x∈
    powerDerivativeApart x _ = inl (snd (realExp x))

    section : ∀ y y∈ →
      powerOnInterval (boundedLn B y y∈) (snd y∈) ≡ y
    section y y∈ = cong fst (realExp-ln (y , fst y∈))

    rawDerivativeValue : ∀ y → y ∈ boundedLogPred B → ℝ
    rawDerivativeValue y y∈ =
      invℝ (fst (realExp (boundedLn B y y∈)))
        (inl (snd (realExp (boundedLn B y y∈))))

    raw≡natural : ∀ y y∈ →
      rawDerivativeValue y y∈ ≡ boundedLnDerivativeValue B y y∈
    raw≡natural y y∈ =
      sym
        (invℝ₊≡invℝ (realExp (boundedLn B y y∈))
          (inl (snd (realExp (boundedLn B y y∈)))))
      ∙ cong (fst ∘ invℝ₊) (realExp-ln (y , fst y∈))

    derive :
      Σ[ m ∈ ℚ₊ ]
        LowerLipschitz-ℝ→ℝℙ m (exponentInterval B) powerOnInterval →
      DerivativeOfℙ boundedLogPred B , boundedLn B is
        boundedLnDerivativeValue B
    derive (m , lower) =
      subst
        (DerivativeOfℙ boundedLogPred B , boundedLn B is_)
        (funExt₂ raw≡natural)
        (inverseDerivativeℙ
          (exponentInterval B) (boundedLogPred B)
          powerOnInterval powerDerivativeValue
          (boundedLn B) (λ _ y∈ → snd y∈) section
          m lower powerDerivativeApart powerDerivative)
