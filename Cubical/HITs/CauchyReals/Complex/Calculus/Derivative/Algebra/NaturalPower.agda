module Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.NaturalPower where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Order.Algebra as ℚA
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚAbs
open import Cubical.Data.Sigma

import Cubical.Algebra.OrderedCommRing.Properties as Ordered
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Order
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.Power
open import Cubical.HITs.CauchyReals.Complex.Modulus.Bounds
open import Cubical.HITs.CauchyReals.Complex.Modulus.BoundAlgebra
open import Cubical.HITs.CauchyReals.Complex.Domain
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Within
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Product

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


private
  module ℚOrder =
    Ordered.OrderedCommRingTheory ℚOrderedCommRing


naturalPowerComplexFunction : ℕ → ℂ → ℂ
naturalPowerComplexFunction n z = z ^ℂ n


positiveNaturalBoundRadius : ℕ → ℚ₊
positiveNaturalBoundRadius n =
  fromNat (suc n)


positiveNaturalComplex : ℕ → ℂ
positiveNaturalComplex n =
  fromℝ (rat (fst (positiveNaturalBoundRadius n)))


naturalPowerDerivative : ℕ → ℂ → ℂ
naturalPowerDerivative zero z =
  0ℂ
naturalPowerDerivative (suc n) z =
  positiveNaturalComplex n
  ·ℂ naturalPowerComplexFunction n z


opaque
  positiveNaturalComplexPath :
    ∀ n →
    positiveNaturalComplex n ≡
    fromℝ (rat (fst (positiveNaturalBoundRadius n)))
  positiveNaturalComplexPath n =
    refl


  positiveNaturalComplexModulusFromRealPath :
    ∀ n →
    modulus (positiveNaturalComplex n) ≡
    absᵣ (rat (fst (positiveNaturalBoundRadius n)))
  positiveNaturalComplexModulusFromRealPath n =
    cong modulus (positiveNaturalComplexPath n)
    ∙ modulus-fromℝ
        (rat (fst (positiveNaturalBoundRadius n)))


  positiveNaturalAbsPath :
    ∀ n →
    absᵣ (rat (fst (positiveNaturalBoundRadius n))) ≡
    rat (fst (positiveNaturalBoundRadius n))
  positiveNaturalAbsPath n =
    absᵣ-rat (fst (positiveNaturalBoundRadius n))
    ∙ cong rat
        (ℚOrder.0<→abs≡id
          (fst (positiveNaturalBoundRadius n))
          (snd (positiveNaturalBoundRadius n)))


  positiveNaturalComplexModulus :
    ∀ n →
    modulus (positiveNaturalComplex n) ≡
    rat (fst (positiveNaturalBoundRadius n))
  positiveNaturalComplexModulus n =
    positiveNaturalComplexModulusFromRealPath n
    ∙ positiveNaturalAbsPath n


positiveNaturalComplexBound :
  ∀ n →
  ComplexScalarBound (positiveNaturalComplex n)
positiveNaturalComplexBound n =
  positiveNaturalBoundRadius n ,
  ≡ᵣWeaken≤ᵣ _ _
    (positiveNaturalComplexModulus n)


opaque
  positiveNaturalComplex-suc :
    ∀ n →
    1ℂ +ℂ positiveNaturalComplex n ≡
    positiveNaturalComplex (suc n)
  positiveNaturalComplex-suc n =
    ℂ≡
      (+ᵣ-rat
        (fst (positiveNaturalBoundRadius zero))
        (fst (positiveNaturalBoundRadius n))
      ∙ cong rat
          (ℚAbs.ℕ+→ℚ+
            1 (suc n)))
      ℝ!


private
  opaque
    naturalPowerFunctionPath :
      (n : ℕ) → (z : ℂ) →
      naturalPowerComplexFunction n z ≡ z ^ℂ n
    naturalPowerFunctionPath n z =
      refl


    naturalPowerFunctionModulusPath :
      (n : ℕ) → (z : ℂ) →
      modulus (naturalPowerComplexFunction n z) ≡
      modulus z ^ⁿ n
    naturalPowerFunctionModulusPath n z =
      cong modulus (naturalPowerFunctionPath n z)
      ∙ modulus-power z n


    naturalPowerValueBound :
      (n : ℕ) → (z : ℂ) → (M : ℚ₊) →
      modulus z ≤ᵣ rat (fst M) →
      modulus (naturalPowerComplexFunction n z)
        ≤ᵣ rat (fst (M ℚA.ℚ₊^ⁿ n))
    naturalPowerValueBound n z M |z|≤M =
      isTrans≡≤ᵣ _ _ _
        (naturalPowerFunctionModulusPath n z)
        (isTrans≤≡ᵣ _ _ _
          (^ⁿ-Monotone n
            (modulusNonNeg z)
            |z|≤M)
          (^ⁿ-ℚ^ⁿ n (fst M)))


    naturalPowerDerivativeSucPath :
      (n : ℕ) → (z : ℂ) →
      naturalPowerDerivative (suc n) z ≡
      positiveNaturalComplex n
        ·ℂ naturalPowerComplexFunction n z
    naturalPowerDerivativeSucPath n z =
      refl


    naturalPowerDerivativeProductBound :
      (n : ℕ) → (z : ℂ) → (M : ℚ₊) →
      modulus z ≤ᵣ rat (fst M) →
      ComplexScalarBound
        (positiveNaturalComplex n
          ·ℂ naturalPowerComplexFunction n z)
    naturalPowerDerivativeProductBound n z M |z|≤M =
      positiveNaturalBoundRadius n
        ·₊ (M ℚA.ℚ₊^ⁿ n) ,
      isTrans≡≤ᵣ _ _ _
        (modulus-mul
          (positiveNaturalComplex n)
          (naturalPowerComplexFunction n z))
        (isTrans≤≡ᵣ _ _ _
          (≤ᵣ₊Monotone·ᵣ
            (modulus (positiveNaturalComplex n))
            (rat (fst (positiveNaturalBoundRadius n)))
            (modulus (naturalPowerComplexFunction n z))
            (rat (fst (M ℚA.ℚ₊^ⁿ n)))
            (<ᵣWeaken≤ᵣ _ _
              (snd
                (ℚ₊→ℝ₊
                  (positiveNaturalBoundRadius n))))
            (modulusNonNeg
              (naturalPowerComplexFunction n z))
            (≡ᵣWeaken≤ᵣ _ _
              (positiveNaturalComplexModulus n))
            (naturalPowerValueBound n z M |z|≤M))
          (sym
            (rat·ᵣrat
              (fst (positiveNaturalBoundRadius n))
              (fst (M ℚA.ℚ₊^ⁿ n)))))


positiveNaturalPowerDerivativeBound :
  ∀ n z →
  ComplexScalarBound z →
  ComplexScalarBound
    (positiveNaturalComplex n
      ·ℂ naturalPowerComplexFunction n z)
positiveNaturalPowerDerivativeBound
  n z (M , |z|≤M) =
  naturalPowerDerivativeProductBound n z M |z|≤M


naturalPowerComplexFunctionBound :
  ∀ n z →
  ComplexScalarBound z →
  ComplexScalarBound (naturalPowerComplexFunction n z)
naturalPowerComplexFunctionBound
  n z (M , |z|≤M) =
  (M ℚA.ℚ₊^ⁿ n) ,
  naturalPowerValueBound n z M |z|≤M


private
  opaque
    naturalPowerFunctionSucPath :
      (n : ℕ) → (z : ℂ) →
      naturalPowerComplexFunction (suc n) z ≡
      z ·ℂ naturalPowerComplexFunction n z
    naturalPowerFunctionSucPath n z =
      refl


    positiveNaturalComplex-zero :
      positiveNaturalComplex zero ≡ 1ℂ
    positiveNaturalComplex-zero =
      ℂ≡ refl refl


    naturalPowerFunctionZeroPath :
      ∀ z →
      naturalPowerComplexFunction zero z ≡ 1ℂ
    naturalPowerFunctionZeroPath z =
      refl


    naturalPowerFunctionOnePath :
      ∀ z →
      naturalPowerComplexFunction (suc zero) z ≡ z
    naturalPowerFunctionOnePath z =
      naturalPowerFunctionSucPath zero z
      ∙ cong (z ·ℂ_)
          (naturalPowerFunctionZeroPath z)
      ∙ ·ℂIdR z


    identityToNaturalPowerOnePath :
      (λ z → z) ≡
      naturalPowerComplexFunction (suc zero)
    identityToNaturalPowerOnePath =
      funExt λ z →
        sym (naturalPowerFunctionOnePath z)


    constantOneToNaturalPowerZeroPath :
      (λ _ → 1ℂ) ≡
      naturalPowerComplexFunction zero
    constantOneToNaturalPowerZeroPath =
      funExt λ z →
        sym (naturalPowerFunctionZeroPath z)


    positiveNaturalPowerDerivativeZeroPath :
      ∀ z →
      1ℂ ≡
      positiveNaturalComplex zero
        ·ℂ naturalPowerComplexFunction zero z
    positiveNaturalPowerDerivativeZeroPath z =
      sym
        (cong₂ _·ℂ_
          positiveNaturalComplex-zero
          (naturalPowerFunctionZeroPath z)
        ∙ ·ℂIdR 1ℂ)

    naturalPowerDerivativeStepUnfoldPath :
      (n : ℕ) → (z : ℂ) →
      (1ℂ ·ℂ naturalPowerComplexFunction (suc n) z
        +ℂ
       z ·ℂ
        (positiveNaturalComplex n
          ·ℂ naturalPowerComplexFunction n z))
      ≡
      (1ℂ ·ℂ
        (z ·ℂ naturalPowerComplexFunction n z)
        +ℂ
       z ·ℂ
        (positiveNaturalComplex n
          ·ℂ naturalPowerComplexFunction n z))
    naturalPowerDerivativeStepUnfoldPath n z =
      cong
        (λ firstTerm →
          firstTerm
          +ℂ z ·ℂ
            (positiveNaturalComplex n
              ·ℂ naturalPowerComplexFunction n z))
        (cong (1ℂ ·ℂ_)
          (naturalPowerFunctionSucPath n z))


    naturalPowerDerivativeStepAlgebra :
      ∀ z c p →
      1ℂ ·ℂ (z ·ℂ p)
        +ℂ z ·ℂ (c ·ℂ p)
      ≡
      (1ℂ +ℂ c) ·ℂ (z ·ℂ p)
    naturalPowerDerivativeStepAlgebra z c p =
      ℂ≡ ℝ! ℝ!


    naturalPowerDerivativeStepFoldPath :
      (n : ℕ) → (z : ℂ) →
      (1ℂ +ℂ positiveNaturalComplex n)
        ·ℂ (z ·ℂ naturalPowerComplexFunction n z)
      ≡
      (1ℂ +ℂ positiveNaturalComplex n)
        ·ℂ naturalPowerComplexFunction (suc n) z
    naturalPowerDerivativeStepFoldPath n z =
      cong
        ((1ℂ +ℂ positiveNaturalComplex n) ·ℂ_)
        (sym (naturalPowerFunctionSucPath n z))


    naturalPowerDerivativeStepCoefficientPath :
      (n : ℕ) → (z : ℂ) →
      (1ℂ +ℂ positiveNaturalComplex n)
        ·ℂ naturalPowerComplexFunction (suc n) z
      ≡
      positiveNaturalComplex (suc n)
        ·ℂ naturalPowerComplexFunction (suc n) z
    naturalPowerDerivativeStepCoefficientPath n z =
      cong
        (_·ℂ naturalPowerComplexFunction (suc n) z)
        (positiveNaturalComplex-suc n)


    naturalPowerProductFunctionPath :
      (n : ℕ) →
      multiplyComplexFunctions
        (λ z → z)
        (naturalPowerComplexFunction (suc n))
      ≡ naturalPowerComplexFunction (suc (suc n))
    naturalPowerProductFunctionPath n =
      funExt λ z →
        sym (naturalPowerFunctionSucPath (suc n) z)


opaque
  positiveNaturalPowerDerivativeStepPath :
    (n : ℕ) → (z : ℂ) →
    (1ℂ ·ℂ naturalPowerComplexFunction (suc n) z
      +ℂ
     z ·ℂ
      (positiveNaturalComplex n
        ·ℂ naturalPowerComplexFunction n z))
    ≡
    positiveNaturalComplex (suc n)
      ·ℂ naturalPowerComplexFunction (suc n) z
  positiveNaturalPowerDerivativeStepPath n z =
    naturalPowerDerivativeStepUnfoldPath n z
    ∙ naturalPowerDerivativeStepAlgebra
        z (positiveNaturalComplex n)
        (naturalPowerComplexFunction n z)
    ∙ naturalPowerDerivativeStepFoldPath n z
    ∙ naturalPowerDerivativeStepCoefficientPath n z


opaque
  hasComplexDerivativeWithinAt-naturalPower-zero :
    ∀ P z →
    HasComplexDerivativeWithinAt P
      (naturalPowerComplexFunction zero)
      0ℂ z
  hasComplexDerivativeWithinAt-naturalPower-zero P z =
    subst
      (λ f →
        HasComplexDerivativeWithinAt P f 0ℂ z)
      constantOneToNaturalPowerZeroPath
      (constantHasDerivativeWithin P 1ℂ z)


opaque
  positiveNaturalPowerOneHasDerivativeWithin :
    ∀ P z →
    HasComplexDerivativeWithinAt P
      (naturalPowerComplexFunction (suc zero))
      (positiveNaturalComplex zero
        ·ℂ naturalPowerComplexFunction zero z)
      z
  positiveNaturalPowerOneHasDerivativeWithin P z =
    subst2
      (λ f derivative →
        HasComplexDerivativeWithinAt P f derivative z)
      identityToNaturalPowerOnePath
      (positiveNaturalPowerDerivativeZeroPath z)
      (identityHasDerivativeWithin P z)


opaque
  positiveNaturalPowerDerivativeStep :
    ∀ P n z →
    HasComplexDerivativeWithinAt P
      (multiplyComplexFunctions
        (λ w → w)
        (naturalPowerComplexFunction (suc n)))
      (1ℂ ·ℂ naturalPowerComplexFunction (suc n) z
        +ℂ
       z ·ℂ
        (positiveNaturalComplex n
          ·ℂ naturalPowerComplexFunction n z))
      z →
    HasComplexDerivativeWithinAt P
      (naturalPowerComplexFunction (suc (suc n)))
      (positiveNaturalComplex (suc n)
        ·ℂ naturalPowerComplexFunction (suc n) z)
      z
  positiveNaturalPowerDerivativeStep P n z derivativeWithin =
    subst2
      (λ f derivative →
        HasComplexDerivativeWithinAt P f derivative z)
      (naturalPowerProductFunctionPath n)
      (positiveNaturalPowerDerivativeStepPath n z)
      derivativeWithin


hasComplexDerivativeWithinAt-positiveNaturalPower :
  ∀ P n z →
  ComplexScalarBound z →
  HasComplexDerivativeWithinAt P
    (naturalPowerComplexFunction (suc n))
    (positiveNaturalComplex n
      ·ℂ naturalPowerComplexFunction n z)
    z
hasComplexDerivativeWithinAt-positiveNaturalPower
  P zero z bound =
  positiveNaturalPowerOneHasDerivativeWithin P z
hasComplexDerivativeWithinAt-positiveNaturalPower
  P (suc n) z bound =
  let
    previousDerivative :
      HasComplexDerivativeWithinAt P
        (naturalPowerComplexFunction (suc n))
        (positiveNaturalComplex n
          ·ℂ naturalPowerComplexFunction n z)
        z
    previousDerivative =
      hasComplexDerivativeWithinAt-positiveNaturalPower
        P n z bound

    productDerivative :
      HasComplexDerivativeWithinAt P
        (multiplyComplexFunctions
          (λ w → w)
          (naturalPowerComplexFunction (suc n)))
        (1ℂ ·ℂ naturalPowerComplexFunction (suc n) z
          +ℂ
         z ·ℂ
          (positiveNaturalComplex n
            ·ℂ naturalPowerComplexFunction n z))
        z
    productDerivative =
      hasComplexDerivativeWithinAt-mul
        {P = P}
        {f = λ w → w}
        {derivativeF = 1ℂ}
        {g = naturalPowerComplexFunction (suc n)}
        {derivativeG =
          positiveNaturalComplex n
            ·ℂ naturalPowerComplexFunction n z}
        {z = z}
        bound
        oneComplexScalarBound
        (naturalPowerComplexFunctionBound
          (suc n) z bound)
        (positiveNaturalPowerDerivativeBound
          n z bound)
        (identityHasDerivativeWithin P z)
        previousDerivative
  in
  positiveNaturalPowerDerivativeStep
    P n z productDerivative


complexDifferentiableWithinAt-naturalPower :
  ∀ P n z →
  ComplexScalarBound z →
  ComplexDifferentiableWithinAt P
    (naturalPowerComplexFunction n) z
complexDifferentiableWithinAt-naturalPower
  P zero z bound =
  0ℂ ,
  hasComplexDerivativeWithinAt-naturalPower-zero P z
complexDifferentiableWithinAt-naturalPower
  P (suc n) z bound =
  (positiveNaturalComplex n
    ·ℂ naturalPowerComplexFunction n z) ,
  hasComplexDerivativeWithinAt-positiveNaturalPower
    P n z bound


holomorphicOn-naturalPower :
  ∀ P n →
  ((z : ℂ) → z ∈ P → ComplexScalarBound z) →
  HolomorphicOn P (naturalPowerComplexFunction n)
holomorphicOn-naturalPower P n bound z z∈P =
  complexDifferentiableWithinAt-naturalPower
    P n z (bound z z∈P)
