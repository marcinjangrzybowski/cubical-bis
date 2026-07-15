module Cubical.HITs.CauchyReals.Exponentiation.RealPower.CalculusProof where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Nat as ℕ hiding (_+_; _·_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Uniqueness
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Scaling
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Construction
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.DerivativeEverywhere
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Composition

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- Previous name: ^-der, for the quotient-slope derivative.
realPowerDerivativeProof : ∀ x →
  DerivativeOfℙ ⊤Pred , (λ y _ → fst (x ^ᵣ y)) is
    (λ y _ → fst (x ^ᵣ y) ·ᵣ ln x)
realPowerDerivativeProof (x , 0<x) =
  Seq-^-FI.∩$-elimProp x 0<x
    {λ (g , d) →
      DerivativeOfℙ ⊤Pred , (λ y _ → fst (g y)) is
        (λ y _ → fst (g y) ·ᵣ d)}
    (λ (g , d) →
      isProp-DerivativeOfℙ ⊤Pred
        (λ y _ → fst (g y))
        (λ y _ → fst (g y) ·ᵣ d))
    λ n (xLower , xUpper) →
      subst
        (λ (g , d) →
          DerivativeOfℙ ⊤Pred , (λ y _ → fst (g y)) is
            (λ y _ → fst (g y) ·ᵣ d))
        (sym (Seq-^-fun≡BDL x n (xLower , xUpper)))
        (BDLDerivativeEverywhere.𝒇-derivative
          (x , isTrans<≤ᵣ 0
            (rat [ pos 1 / fromNat (suc (suc n)) ]) x
            (<ℚ→<ᵣ [ pos 0 / 1 ]
              [ pos 1 / fromNat (suc (suc n)) ]
              (ℚ.0<pos 0 (fromNat (suc (suc n)))))
            xLower)
          n xUpper xLower)

-- Previous names: ln[a^b₊]≡b₊·ln[a], ln[a^b]≡b·ln[a].
ln-realPowerProof : ∀ a b → ln (a ^ᵣ b) ≡ b ·ᵣ ln a
ln-realPowerProof a b =
  sym leftAtZero
  ∙ derivativeValueUnique powered powerDerivative scaledDerivative
      directDerivative scaledDerivativeOnPowered 0
  ∙ rightAtZero
  ∙ ·ᵣComm (ln a) b
  where
  powered : ℝ → ℝ
  powered r = fst ((a ^ᵣ b) ^ᵣ r)

  scaled : ℝ → ℝ
  scaled r = fst (a ^ᵣ (b ·ᵣ r))

  powerDerivative : ℝ → ℝ
  powerDerivative r = powered r ·ᵣ ln (a ^ᵣ b)

  scaledDerivative : ℝ → ℝ
  scaledDerivative r = (fst (a ^ᵣ (b ·ᵣ r)) ·ᵣ ln a) ·ᵣ b

  powered≡scaled :
    (λ r (_ : r ∈ ⊤Pred) → powered r) ≡
    (λ r (_ : r ∈ ⊤Pred) → scaled r)
  powered≡scaled = funExt₂ λ r _ → realPowerMulExponent a b r

  directDerivative :
    DerivativeOfℙ ⊤Pred , (λ r _ → powered r) is
      (λ r _ → powerDerivative r)
  directDerivative = realPowerDerivativeProof (a ^ᵣ b)

  scaledDerivativeProof :
    DerivativeOfℙ ⊤Pred , (λ r _ → scaled r) is
      (λ r _ → scaledDerivative r)
  scaledDerivativeProof =
    scaleInputDerivative b
      (λ r → fst (a ^ᵣ r))
      (λ r → fst (a ^ᵣ r) ·ᵣ ln a)
      (realPowerDerivativeProof a)

  scaledDerivativeOnPowered :
    DerivativeOfℙ ⊤Pred , (λ r _ → powered r) is
      (λ r _ → scaledDerivative r)
  scaledDerivativeOnPowered =
    subst
      (λ h → DerivativeOfℙ ⊤Pred , h is
        (λ r _ → scaledDerivative r))
      (sym powered≡scaled)
      scaledDerivativeProof

  leftAtZero : powerDerivative 0 ≡ ln (a ^ᵣ b)
  leftAtZero =
    cong (_·ᵣ ln (a ^ᵣ b)) (^ᵣ0 (a ^ᵣ b))
    ∙ ·IdLᵣ (ln (a ^ᵣ b))

  rightAtZero : scaledDerivative 0 ≡ ln a ·ᵣ b
  rightAtZero =
    cong (_·ᵣ b)
      (cong (_·ᵣ ln a)
        (cong (fst ∘ (a ^ᵣ_)) (Rℝ.0RightAnnihilates b)
         ∙ ^ᵣ0 a)
       ∙ ·IdLᵣ (ln a))
