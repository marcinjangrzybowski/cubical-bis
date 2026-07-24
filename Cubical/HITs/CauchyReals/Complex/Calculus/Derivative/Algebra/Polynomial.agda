module Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Polynomial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Bounds
open import Cubical.HITs.CauchyReals.Complex.Modulus.BoundAlgebra
open import Cubical.HITs.CauchyReals.Complex.Domain
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Within
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Addition
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Product

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


private
  evaluatePolynomialRaw : List ℂ → ℂ → ℂ
  evaluatePolynomialRaw [] z =
    0ℂ
  evaluatePolynomialRaw (a ∷ coefficients) z =
    a +ℂ z ·ℂ evaluatePolynomialRaw coefficients z


  evaluatePolynomialDerivativeRaw : List ℂ → ℂ → ℂ
  evaluatePolynomialDerivativeRaw [] z =
    0ℂ
  evaluatePolynomialDerivativeRaw (a ∷ coefficients) z =
    evaluatePolynomialRaw coefficients z
    +ℂ z ·ℂ evaluatePolynomialDerivativeRaw coefficients z


-- Coefficients are stored in increasing degree order.  Thus
-- `a ∷ b ∷ []` evaluates to `a + b · z`.
opaque
  evaluatePolynomial : List ℂ → ℂ → ℂ
  evaluatePolynomial coefficients z =
    evaluatePolynomialRaw coefficients z


  evaluatePolynomial-empty :
    ∀ z →
    evaluatePolynomial [] z ≡ 0ℂ
  evaluatePolynomial-empty z =
    refl


  evaluatePolynomial-cons :
    ∀ a coefficients z →
    evaluatePolynomial (a ∷ coefficients) z ≡
    a +ℂ z ·ℂ evaluatePolynomial coefficients z
  evaluatePolynomial-cons a coefficients z =
    refl


  evaluatePolynomialDerivative : List ℂ → ℂ → ℂ
  evaluatePolynomialDerivative coefficients z =
    evaluatePolynomialDerivativeRaw coefficients z


  evaluatePolynomialDerivative-empty :
    ∀ z →
    evaluatePolynomialDerivative [] z ≡ 0ℂ
  evaluatePolynomialDerivative-empty z =
    refl


  evaluatePolynomialDerivative-cons :
    ∀ a coefficients z →
    evaluatePolynomialDerivative (a ∷ coefficients) z ≡
    evaluatePolynomial coefficients z
      +ℂ z ·ℂ evaluatePolynomialDerivative coefficients z
  evaluatePolynomialDerivative-cons a coefficients z =
    refl
-- A product-rule proof for one Horner step needs bounds for the value and
-- derivative of its tail.  This certificate stores exactly those bounds at
-- every nonempty recursive tail.
PolynomialTailBoundsAt : ℂ → List ℂ → Type₀
PolynomialTailBoundsAt z [] =
  Unit
PolynomialTailBoundsAt z (a ∷ coefficients) =
  ComplexScalarBound (evaluatePolynomial coefficients z)
  × ComplexScalarBound
      (evaluatePolynomialDerivative coefficients z)
  × PolynomialTailBoundsAt z coefficients


opaque
  emptyPolynomialValueBound :
    ∀ z →
    ComplexScalarBound (evaluatePolynomial [] z)
  emptyPolynomialValueBound z =
    subst ComplexScalarBound
      (sym (evaluatePolynomial-empty z))
      zeroComplexScalarBound


  emptyPolynomialDerivativeBound :
    ∀ z →
    ComplexScalarBound
      (evaluatePolynomialDerivative [] z)
  emptyPolynomialDerivativeBound z =
    subst ComplexScalarBound
      (sym (evaluatePolynomialDerivative-empty z))
      zeroComplexScalarBound


emptyPolynomialTailBoundsAt :
  ∀ z →
  PolynomialTailBoundsAt z []
emptyPolynomialTailBoundsAt z =
  tt


singletonPolynomialTailBoundsAt :
  ∀ z a →
  PolynomialTailBoundsAt z (a ∷ [])
singletonPolynomialTailBoundsAt z a =
  emptyPolynomialValueBound z ,
  emptyPolynomialDerivativeBound z ,
  emptyPolynomialTailBoundsAt z


opaque
  evaluatePolynomial-singleton :
    ∀ a z →
    evaluatePolynomial (a ∷ []) z ≡ a
  evaluatePolynomial-singleton a z =
    evaluatePolynomial-cons a [] z
    ∙ cong
        (λ tailValue →
          a +ℂ z ·ℂ tailValue)
        (evaluatePolynomial-empty z)
    ∙ ℂ≡ ℝ! ℝ!


  evaluatePolynomialDerivative-singleton :
    ∀ a z →
    evaluatePolynomialDerivative (a ∷ []) z ≡ 0ℂ
  evaluatePolynomialDerivative-singleton a z =
    evaluatePolynomialDerivative-cons a [] z
    ∙ cong₂ _+ℂ_
        (evaluatePolynomial-empty z)
        (cong (z ·ℂ_)
          (evaluatePolynomialDerivative-empty z))
    ∙ ℂ≡ ℝ! ℝ!


opaque
  singletonPolynomialValueBound :
    ∀ a z →
    ComplexScalarBound a →
    ComplexScalarBound
      (evaluatePolynomial (a ∷ []) z)
  singletonPolynomialValueBound a z aBound =
    subst ComplexScalarBound
      (sym (evaluatePolynomial-singleton a z))
      aBound


  singletonPolynomialDerivativeBound :
    ∀ a z →
    ComplexScalarBound
      (evaluatePolynomialDerivative (a ∷ []) z)
  singletonPolynomialDerivativeBound a z =
    subst ComplexScalarBound
      (sym
        (evaluatePolynomialDerivative-singleton a z))
      zeroComplexScalarBound


linearPolynomialTailBoundsAt :
  ∀ z a b →
  ComplexScalarBound a →
  PolynomialTailBoundsAt z (b ∷ a ∷ [])
linearPolynomialTailBoundsAt z a b aBound =
  singletonPolynomialValueBound a z aBound ,
  singletonPolynomialDerivativeBound a z ,
  singletonPolynomialTailBoundsAt z a


opaque
  evaluatePolynomialDerivative-linear :
    ∀ a b z →
    evaluatePolynomialDerivative (b ∷ a ∷ []) z ≡ a
  evaluatePolynomialDerivative-linear a b z =
    evaluatePolynomialDerivative-cons b (a ∷ []) z
    ∙ cong₂ _+ℂ_
        (evaluatePolynomial-singleton a z)
        (cong (z ·ℂ_)
          (evaluatePolynomialDerivative-singleton a z))
    ∙ ℂ≡ ℝ! ℝ!


private
  opaque
    polynomialEmptyFunctionPath :
      (λ _ → 0ℂ) ≡ evaluatePolynomial []
    polynomialEmptyFunctionPath =
      funExt λ z →
        sym (evaluatePolynomial-empty z)


    polynomialEmptyDerivativePath :
      ∀ z →
      0ℂ ≡ evaluatePolynomialDerivative [] z
    polynomialEmptyDerivativePath z =
      sym (evaluatePolynomialDerivative-empty z)


    polynomialEmptyDerivative :
      ∀ P z →
      HasComplexDerivativeWithinAt P
        (λ _ → 0ℂ) 0ℂ z →
      HasComplexDerivativeWithinAt P
        (evaluatePolynomial [])
        (evaluatePolynomialDerivative [] z)
        z
    polynomialEmptyDerivative P z derivativeWithin =
      subst2
        (λ f derivative →
          HasComplexDerivativeWithinAt P f derivative z)
        polynomialEmptyFunctionPath
        (polynomialEmptyDerivativePath z)
        derivativeWithin


    polynomialHornerStepPath :
      ∀ a coefficients →
      addComplexFunctions
        (λ _ → a)
        (multiplyComplexFunctions
          (λ z → z)
          (evaluatePolynomial coefficients))
      ≡
      evaluatePolynomial (a ∷ coefficients)
    polynomialHornerStepPath a coefficients =
      funExt λ z →
        sym (evaluatePolynomial-cons a coefficients z)


    polynomialDerivativeStepPath :
      ∀ z tailValue tailDerivative →
      0ℂ
        +ℂ
      (1ℂ ·ℂ tailValue
        +ℂ z ·ℂ tailDerivative)
      ≡
      tailValue +ℂ z ·ℂ tailDerivative
    polynomialDerivativeStepPath z tailValue tailDerivative =
      ℂ≡ ℝ! ℝ!


    polynomialFunctionStep :
      ∀ P a coefficients derivative z →
      HasComplexDerivativeWithinAt P
        (addComplexFunctions
          (λ _ → a)
          (multiplyComplexFunctions
            (λ w → w)
            (evaluatePolynomial coefficients)))
        derivative z →
      HasComplexDerivativeWithinAt P
        (evaluatePolynomial (a ∷ coefficients))
        derivative z
    polynomialFunctionStep
      P a coefficients derivative z derivativeWithin =
      subst
        (λ f →
          HasComplexDerivativeWithinAt P f derivative z)
        (polynomialHornerStepPath a coefficients)
        derivativeWithin


    polynomialDerivativeStep :
      ∀ P a coefficients z →
      HasComplexDerivativeWithinAt P
        (evaluatePolynomial (a ∷ coefficients))
        (0ℂ
          +ℂ
        (1ℂ ·ℂ evaluatePolynomial coefficients z
          +ℂ
         z ·ℂ evaluatePolynomialDerivative coefficients z))
        z →
      HasComplexDerivativeWithinAt P
        (evaluatePolynomial (a ∷ coefficients))
        (evaluatePolynomialDerivative (a ∷ coefficients) z)
        z
    polynomialDerivativeStep
      P a coefficients z derivativeWithin =
      subst
        (λ derivative →
          HasComplexDerivativeWithinAt P
            (evaluatePolynomial (a ∷ coefficients))
            derivative z)
        (polynomialDerivativeStepPath
          z
          (evaluatePolynomial coefficients z)
          (evaluatePolynomialDerivative coefficients z)
        ∙ sym
            (evaluatePolynomialDerivative-cons
              a coefficients z))
        derivativeWithin


opaque
  polynomialTailProductHasDerivativeWithin :
    ∀ P coefficients z →
    ComplexScalarBound z →
    ComplexScalarBound (evaluatePolynomial coefficients z) →
    ComplexScalarBound
      (evaluatePolynomialDerivative coefficients z) →
    HasComplexDerivativeWithinAt P
      (evaluatePolynomial coefficients)
      (evaluatePolynomialDerivative coefficients z)
      z →
    HasComplexDerivativeWithinAt P
      (multiplyComplexFunctions
        (λ w → w)
        (evaluatePolynomial coefficients))
      (1ℂ ·ℂ evaluatePolynomial coefficients z
        +ℂ
       z ·ℂ evaluatePolynomialDerivative coefficients z)
      z
  polynomialTailProductHasDerivativeWithin
    P coefficients z zBound
    tailValueBound tailDerivativeBound tailDerivativeWithin =
    hasComplexDerivativeWithinAt-mul
      {P = P}
      {f = λ w → w}
      {derivativeF = 1ℂ}
      {g = evaluatePolynomial coefficients}
      {derivativeG =
        evaluatePolynomialDerivative coefficients z}
      {z = z}
      zBound
      oneComplexScalarBound
      tailValueBound
      tailDerivativeBound
      (identityHasDerivativeWithin P z)
      tailDerivativeWithin


opaque
  polynomialHornerHasDerivativeWithin :
    ∀ P a coefficients z →
    HasComplexDerivativeWithinAt P
      (multiplyComplexFunctions
        (λ w → w)
        (evaluatePolynomial coefficients))
      (1ℂ ·ℂ evaluatePolynomial coefficients z
        +ℂ
       z ·ℂ evaluatePolynomialDerivative coefficients z)
      z →
    HasComplexDerivativeWithinAt P
      (addComplexFunctions
        (λ _ → a)
        (multiplyComplexFunctions
          (λ w → w)
          (evaluatePolynomial coefficients)))
      (0ℂ
        +ℂ
      (1ℂ ·ℂ evaluatePolynomial coefficients z
        +ℂ
       z ·ℂ evaluatePolynomialDerivative coefficients z))
      z
  polynomialHornerHasDerivativeWithin
    P a coefficients z productDerivativeWithin =
    hasComplexDerivativeWithinAt-add
      {P = P}
      {f = λ _ → a}
      {derivativeF = 0ℂ}
      {g =
        multiplyComplexFunctions
          (λ w → w)
          (evaluatePolynomial coefficients)}
      {derivativeG =
        1ℂ ·ℂ evaluatePolynomial coefficients z
          +ℂ
        z ·ℂ evaluatePolynomialDerivative coefficients z}
      {z = z}
      (constantHasDerivativeWithin P a z)
      productDerivativeWithin


opaque
  polynomialHornerToConsHasDerivativeWithin :
    ∀ P a coefficients z →
    HasComplexDerivativeWithinAt P
      (addComplexFunctions
        (λ _ → a)
        (multiplyComplexFunctions
          (λ w → w)
          (evaluatePolynomial coefficients)))
      (0ℂ
        +ℂ
      (1ℂ ·ℂ evaluatePolynomial coefficients z
        +ℂ
       z ·ℂ evaluatePolynomialDerivative coefficients z))
      z →
    HasComplexDerivativeWithinAt P
      (evaluatePolynomial (a ∷ coefficients))
      (evaluatePolynomialDerivative (a ∷ coefficients) z)
      z
  polynomialHornerToConsHasDerivativeWithin
    P a coefficients z hornerDerivativeWithin =
    polynomialDerivativeStep
      P a coefficients z
      (polynomialFunctionStep
        P a coefficients
        (0ℂ
          +ℂ
        (1ℂ ·ℂ evaluatePolynomial coefficients z
          +ℂ
         z ·ℂ evaluatePolynomialDerivative coefficients z))
        z hornerDerivativeWithin)


opaque
  polynomialConsHasDerivativeWithin :
    ∀ P a coefficients z →
    ComplexScalarBound z →
    ComplexScalarBound (evaluatePolynomial coefficients z) →
    ComplexScalarBound
      (evaluatePolynomialDerivative coefficients z) →
    HasComplexDerivativeWithinAt P
      (evaluatePolynomial coefficients)
      (evaluatePolynomialDerivative coefficients z)
      z →
    HasComplexDerivativeWithinAt P
      (evaluatePolynomial (a ∷ coefficients))
      (evaluatePolynomialDerivative (a ∷ coefficients) z)
      z
  polynomialConsHasDerivativeWithin
    P a coefficients z zBound
    tailValueBound tailDerivativeBound tailDerivativeWithin =
    polynomialHornerToConsHasDerivativeWithin
      P a coefficients z
      (polynomialHornerHasDerivativeWithin
        P a coefficients z
        (polynomialTailProductHasDerivativeWithin
          P coefficients z
          zBound tailValueBound tailDerivativeBound
          tailDerivativeWithin))


hasComplexDerivativeWithinAt-polynomial :
  ∀ P coefficients z →
  ComplexScalarBound z →
  PolynomialTailBoundsAt z coefficients →
  HasComplexDerivativeWithinAt P
    (evaluatePolynomial coefficients)
    (evaluatePolynomialDerivative coefficients z)
    z
hasComplexDerivativeWithinAt-polynomial
  P [] z zBound tailBounds =
  polynomialEmptyDerivative
    P z
    (constantHasDerivativeWithin P 0ℂ z)
hasComplexDerivativeWithinAt-polynomial
  P (a ∷ coefficients) z zBound
  (tailValueBound , tailDerivativeBound , remainingTailBounds) =
  polynomialConsHasDerivativeWithin
    P a coefficients z
    zBound tailValueBound tailDerivativeBound
    (hasComplexDerivativeWithinAt-polynomial
      P coefficients z zBound remainingTailBounds)


opaque
  hasComplexDerivativeWithinAt-linearPolynomial :
    ∀ P a b z →
    ComplexScalarBound z →
    ComplexScalarBound a →
    HasComplexDerivativeWithinAt P
      (evaluatePolynomial (b ∷ a ∷ []))
      a z
  hasComplexDerivativeWithinAt-linearPolynomial
    P a b z zBound aBound =
    subst
      (λ derivative →
        HasComplexDerivativeWithinAt P
          (evaluatePolynomial (b ∷ a ∷ []))
          derivative z)
      (evaluatePolynomialDerivative-linear a b z)
      (hasComplexDerivativeWithinAt-polynomial
        P (b ∷ a ∷ []) z zBound
        (linearPolynomialTailBoundsAt z a b aBound))


complexDifferentiableWithinAt-polynomial :
  ∀ P coefficients z →
  ComplexScalarBound z →
  PolynomialTailBoundsAt z coefficients →
  ComplexDifferentiableWithinAt P
    (evaluatePolynomial coefficients) z
complexDifferentiableWithinAt-polynomial
  P coefficients z zBound tailBounds =
  evaluatePolynomialDerivative coefficients z ,
  hasComplexDerivativeWithinAt-polynomial
    P coefficients z zBound tailBounds


holomorphicOn-polynomial :
  ∀ P coefficients →
  ((z : ℂ) → z ∈ P → ComplexScalarBound z) →
  ((z : ℂ) → z ∈ P →
    PolynomialTailBoundsAt z coefficients) →
  HolomorphicOn P (evaluatePolynomial coefficients)
holomorphicOn-polynomial
  P coefficients zBound tailBounds z z∈P =
  complexDifferentiableWithinAt-polynomial
    P coefficients z
    (zBound z z∈P)
    (tailBounds z z∈P)
