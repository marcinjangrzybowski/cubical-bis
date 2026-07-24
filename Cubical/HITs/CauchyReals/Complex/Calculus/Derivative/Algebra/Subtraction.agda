module Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Subtraction where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Domain
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Within
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Addition
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Negation


subtractComplexFunctions : (ℂ → ℂ) → (ℂ → ℂ) → ℂ → ℂ
subtractComplexFunctions f g =
  addComplexFunctions f (negateComplexFunction g)


opaque
  negatedDerivativeForSubtraction :
    ∀ {P g derivativeG z} →
    HasComplexDerivativeWithinAt P g derivativeG z →
    HasComplexDerivativeWithinAt P
      (negateComplexFunction g) (-ℂ derivativeG) z
  negatedDerivativeForSubtraction
    {P} {g} {derivativeG} {z} derivativeGAt =
    hasComplexDerivativeWithinAt-neg
      {P = P} {f = g} {derivative = derivativeG} {z = z}
      derivativeGAt


opaque
  subtractComplexFunctionsAsAddition : ∀ f g →
    subtractComplexFunctions f g ≡
    addComplexFunctions f (negateComplexFunction g)
  subtractComplexFunctionsAsAddition f g = refl


hasComplexDerivativeWithinAt-sub :
  ∀ {P f derivativeF g derivativeG z} →
  HasComplexDerivativeWithinAt P f derivativeF z →
  HasComplexDerivativeWithinAt P g derivativeG z →
  HasComplexDerivativeWithinAt P
    (subtractComplexFunctions f g)
    (derivativeF +ℂ (-ℂ derivativeG)) z
hasComplexDerivativeWithinAt-sub
  {P} {f} {derivativeF} {g} {derivativeG} {z}
  derivativeFAt derivativeGAt =
  let
    addedNegationDerivative :
      HasComplexDerivativeWithinAt P
        (addComplexFunctions f (negateComplexFunction g))
        (derivativeF +ℂ (-ℂ derivativeG)) z
    addedNegationDerivative =
      hasComplexDerivativeWithinAt-add
        {P = P} {f = f} {derivativeF = derivativeF}
        {g = negateComplexFunction g} {derivativeG = -ℂ derivativeG}
        {z = z}
        derivativeFAt
        (negatedDerivativeForSubtraction
          {P = P} {g = g} {derivativeG = derivativeG} {z = z}
          derivativeGAt)
  in
  subst
    (λ operation →
      HasComplexDerivativeWithinAt P operation
        (derivativeF +ℂ (-ℂ derivativeG)) z)
    (sym (subtractComplexFunctionsAsAddition f g))
    addedNegationDerivative


complexDifferentiableWithinAt-sub :
  ∀ {P f g z} →
  ComplexDifferentiableWithinAt P f z →
  ComplexDifferentiableWithinAt P g z →
  ComplexDifferentiableWithinAt P (subtractComplexFunctions f g) z
complexDifferentiableWithinAt-sub
  {P} {f} {g} {z} differentiableF differentiableG =
  fst differentiableF +ℂ (-ℂ fst differentiableG) ,
  hasComplexDerivativeWithinAt-sub
    {P = P} {f = f} {derivativeF = fst differentiableF}
    {g = g} {derivativeG = fst differentiableG} {z = z}
    (snd differentiableF) (snd differentiableG)


holomorphicOn-sub :
  ∀ {P f g} →
  HolomorphicOn P f → HolomorphicOn P g →
  HolomorphicOn P (subtractComplexFunctions f g)
holomorphicOn-sub {P} {f} {g} holomorphicF holomorphicG z z∈P =
  complexDifferentiableWithinAt-sub
    {P = P} {f = f} {g = g} {z = z}
    (holomorphicF z z∈P) (holomorphicG z z∈P)
