module Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Bounds
open import Cubical.HITs.CauchyReals.Complex.Domain
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Within
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Product
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Inverse


opaque
  quotientComplexFunctions :
    (ℂ → ℂ) → (ℂ → ℂ) → ℂ → ℂ
  quotientComplexFunctions numerator reciprocalDenominator z =
    numerator z ·ℂ reciprocalDenominator z


  quotientComplexFunctions-value :
    ∀ numerator reciprocalDenominator z →
    quotientComplexFunctions
      numerator reciprocalDenominator z
    ≡
    numerator z ·ℂ reciprocalDenominator z
  quotientComplexFunctions-value
    numerator reciprocalDenominator z =
    refl


  quotientDerivative :
    (ℂ → ℂ) → ℂ → (ℂ → ℂ) → ℂ → ℂ → ℂ
  quotientDerivative
    numerator derivativeNumerator
    reciprocalDenominator derivativeDenominator z =
    derivativeNumerator ·ℂ reciprocalDenominator z
    +ℂ
    numerator z
      ·ℂ reciprocalDerivative
        reciprocalDenominator derivativeDenominator z


  quotientDerivative-value :
    ∀ numerator derivativeNumerator
    reciprocalDenominator derivativeDenominator z →
    quotientDerivative
      numerator derivativeNumerator
      reciprocalDenominator derivativeDenominator z
    ≡
    derivativeNumerator ·ℂ reciprocalDenominator z
      +ℂ
    numerator z
      ·ℂ reciprocalDerivative
        reciprocalDenominator derivativeDenominator z
  quotientDerivative-value
    numerator derivativeNumerator
    reciprocalDenominator derivativeDenominator z =
    refl


private
  opaque
    quotientFunctionPath :
      ∀ numerator reciprocalDenominator →
      multiplyComplexFunctions
        numerator reciprocalDenominator
      ≡
      quotientComplexFunctions
        numerator reciprocalDenominator
    quotientFunctionPath numerator reciprocalDenominator =
      funExt λ z →
        sym
          (quotientComplexFunctions-value
            numerator reciprocalDenominator z)


    quotientDerivativePath :
      ∀ numerator derivativeNumerator
      reciprocalDenominator derivativeDenominator z →
      derivativeNumerator ·ℂ reciprocalDenominator z
        +ℂ
      numerator z
        ·ℂ reciprocalDerivative
          reciprocalDenominator derivativeDenominator z
      ≡
      quotientDerivative
        numerator derivativeNumerator
        reciprocalDenominator derivativeDenominator z
    quotientDerivativePath
      numerator derivativeNumerator
      reciprocalDenominator derivativeDenominator z =
      sym
        (quotientDerivative-value
          numerator derivativeNumerator
          reciprocalDenominator derivativeDenominator z)


    quotientDerivativeTransport :
      ∀ P numerator derivativeNumerator
      reciprocalDenominator derivativeDenominator z →
      HasComplexDerivativeWithinAt P
        (multiplyComplexFunctions
          numerator reciprocalDenominator)
        (derivativeNumerator ·ℂ reciprocalDenominator z
          +ℂ
        numerator z
          ·ℂ reciprocalDerivative
            reciprocalDenominator derivativeDenominator z)
        z →
      HasComplexDerivativeWithinAt P
        (quotientComplexFunctions
          numerator reciprocalDenominator)
        (quotientDerivative
          numerator derivativeNumerator
          reciprocalDenominator derivativeDenominator z)
        z
    quotientDerivativeTransport
      P numerator derivativeNumerator
      reciprocalDenominator derivativeDenominator z
      derivativeWithin =
      subst2
        (λ function derivative →
          HasComplexDerivativeWithinAt P
            function derivative z)
        (quotientFunctionPath
          numerator reciprocalDenominator)
        (quotientDerivativePath
          numerator derivativeNumerator
          reciprocalDenominator derivativeDenominator z)
        derivativeWithin


hasComplexDerivativeWithinAt-quotient :
  ∀ {P numerator derivativeNumerator
    denominator derivativeDenominator
    reciprocalDenominator z} →
  ReciprocalOn P denominator reciprocalDenominator →
  z ∈ P →
  ComplexScalarBound derivativeDenominator →
  ComplexScalarBound (reciprocalDenominator z) →
  ComplexLocalBoundWithinAt P reciprocalDenominator z →
  ComplexScalarBound (numerator z) →
  ComplexScalarBound derivativeNumerator →
  ComplexScalarBound
    (reciprocalDerivative
      reciprocalDenominator derivativeDenominator z) →
  HasComplexDerivativeWithinAt P
    numerator derivativeNumerator z →
  HasComplexDerivativeWithinAt P
    denominator derivativeDenominator z →
  HasComplexDerivativeWithinAt P
    (quotientComplexFunctions
      numerator reciprocalDenominator)
    (quotientDerivative
      numerator derivativeNumerator
      reciprocalDenominator derivativeDenominator z)
    z
hasComplexDerivativeWithinAt-quotient
  {P} {numerator} {derivativeNumerator}
  {denominator} {derivativeDenominator}
  {reciprocalDenominator} {z}
  reciprocal z∈P
  derivativeDenominatorBound
  reciprocalValueBound reciprocalLocalBound
  numeratorValueBound numeratorDerivativeBound
  reciprocalDerivativeBound
  numeratorDerivativeWithin denominatorDerivativeWithin =
  let
    inverseDerivativeWithin :
      HasComplexDerivativeWithinAt P
        reciprocalDenominator
        (reciprocalDerivative
          reciprocalDenominator derivativeDenominator z)
        z
    inverseDerivativeWithin =
      hasComplexDerivativeWithinAt-reciprocal
        {P = P}
        {f = denominator}
        {derivativeF = derivativeDenominator}
        {g = reciprocalDenominator}
        {z = z}
        reciprocal z∈P
        derivativeDenominatorBound
        reciprocalValueBound reciprocalLocalBound
        denominatorDerivativeWithin

    productDerivativeWithin :
      HasComplexDerivativeWithinAt P
        (multiplyComplexFunctions
          numerator reciprocalDenominator)
        (derivativeNumerator ·ℂ reciprocalDenominator z
          +ℂ
        numerator z
          ·ℂ reciprocalDerivative
            reciprocalDenominator derivativeDenominator z)
        z
    productDerivativeWithin =
      hasComplexDerivativeWithinAt-mul
        {P = P}
        {f = numerator}
        {derivativeF = derivativeNumerator}
        {g = reciprocalDenominator}
        {derivativeG =
          reciprocalDerivative
            reciprocalDenominator derivativeDenominator z}
        {z = z}
        numeratorValueBound numeratorDerivativeBound
        reciprocalValueBound reciprocalDerivativeBound
        numeratorDerivativeWithin inverseDerivativeWithin
  in
  quotientDerivativeTransport
    P numerator derivativeNumerator
    reciprocalDenominator derivativeDenominator z
    productDerivativeWithin


complexDifferentiableWithinAt-quotient :
  ∀ {P numerator denominator reciprocalDenominator z}
  (differentiableNumerator :
    ComplexDifferentiableWithinAt P numerator z)
  (differentiableDenominator :
    ComplexDifferentiableWithinAt P denominator z) →
  ReciprocalOn P denominator reciprocalDenominator →
  z ∈ P →
  ComplexScalarBound (fst differentiableDenominator) →
  ComplexScalarBound (reciprocalDenominator z) →
  ComplexLocalBoundWithinAt P reciprocalDenominator z →
  ComplexScalarBound (numerator z) →
  ComplexScalarBound (fst differentiableNumerator) →
  ComplexScalarBound
    (reciprocalDerivative
      reciprocalDenominator
      (fst differentiableDenominator) z) →
  ComplexDifferentiableWithinAt P
    (quotientComplexFunctions
      numerator reciprocalDenominator)
    z
complexDifferentiableWithinAt-quotient
  {P} {numerator} {denominator}
  {reciprocalDenominator} {z}
  differentiableNumerator differentiableDenominator
  reciprocal z∈P
  derivativeDenominatorBound
  reciprocalValueBound reciprocalLocalBound
  numeratorValueBound numeratorDerivativeBound
  reciprocalDerivativeBound =
  quotientDerivative
    numerator (fst differentiableNumerator)
    reciprocalDenominator
    (fst differentiableDenominator) z ,
  hasComplexDerivativeWithinAt-quotient
    {P = P}
    {numerator = numerator}
    {derivativeNumerator =
      fst differentiableNumerator}
    {denominator = denominator}
    {derivativeDenominator =
      fst differentiableDenominator}
    {reciprocalDenominator = reciprocalDenominator}
    {z = z}
    reciprocal z∈P
    derivativeDenominatorBound
    reciprocalValueBound reciprocalLocalBound
    numeratorValueBound numeratorDerivativeBound
    reciprocalDerivativeBound
    (snd differentiableNumerator)
    (snd differentiableDenominator)


holomorphicOn-quotient :
  ∀ {P numerator denominator reciprocalDenominator}
  (holomorphicNumerator :
    HolomorphicOn P numerator)
  (holomorphicDenominator :
    HolomorphicOn P denominator) →
  ReciprocalOn P denominator reciprocalDenominator →
  ((z : ℂ) → (z∈P : z ∈ P) →
    ComplexScalarBound
      (fst (holomorphicDenominator z z∈P))) →
  ((z : ℂ) → z ∈ P →
    ComplexScalarBound (reciprocalDenominator z)) →
  ((z : ℂ) → z ∈ P →
    ComplexLocalBoundWithinAt
      P reciprocalDenominator z) →
  ((z : ℂ) → z ∈ P →
    ComplexScalarBound (numerator z)) →
  ((z : ℂ) → (z∈P : z ∈ P) →
    ComplexScalarBound
      (fst (holomorphicNumerator z z∈P))) →
  ((z : ℂ) → (z∈P : z ∈ P) →
    ComplexScalarBound
      (reciprocalDerivative
        reciprocalDenominator
        (fst (holomorphicDenominator z z∈P))
        z)) →
  HolomorphicOn P
    (quotientComplexFunctions
      numerator reciprocalDenominator)
holomorphicOn-quotient
  {P} {numerator} {denominator}
  {reciprocalDenominator}
  holomorphicNumerator holomorphicDenominator
  reciprocal
  derivativeDenominatorBound
  reciprocalValueBound reciprocalLocalBound
  numeratorValueBound numeratorDerivativeBound
  reciprocalDerivativeBound
  z z∈P =
  complexDifferentiableWithinAt-quotient
    {P = P}
    {numerator = numerator}
    {denominator = denominator}
    {reciprocalDenominator = reciprocalDenominator}
    {z = z}
    (holomorphicNumerator z z∈P)
    (holomorphicDenominator z z∈P)
    reciprocal z∈P
    (derivativeDenominatorBound z z∈P)
    (reciprocalValueBound z z∈P)
    (reciprocalLocalBound z z∈P)
    (numeratorValueBound z z∈P)
    (numeratorDerivativeBound z z∈P)
    (reciprocalDerivativeBound z z∈P)
