module Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Negation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Inverse.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Domain
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Within

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


negateComplexFunction : (ℂ → ℂ) → ℂ → ℂ
negateComplexFunction f z = -ℂ f z


negDifferencePath : ∀ x y →
  (-ℂ x) -ℂ (-ℂ y) ≡ -ℂ (x -ℂ y)
negDifferencePath x y =
  ℂ≡ ℝ! ℝ!


negDifferenceNumerator :
  ∀ f z h →
  negateComplexFunction f (z +ℂ h)
    -ℂ negateComplexFunction f z ≡
  -ℂ (f (z +ℂ h) -ℂ f z)
negDifferenceNumerator f z h =
  negDifferencePath (f (z +ℂ h)) (f z)


negDivide :
  ∀ x h (0#h : 0ℂ #ℂ h) →
  (-ℂ x) ／ℂ[ h , 0#h ] ≡
  -ℂ (x ／ℂ[ h , 0#h ])
negDivide x h 0#h =
  Cℂ.-DistL· x (invℂ h 0#h)


negDifferenceQuotient :
  ∀ f z h (0#h : 0ℂ #ℂ h) →
  DifferenceQuotient (negateComplexFunction f) z h 0#h ≡
  -ℂ DifferenceQuotient f z h 0#h
negDifferenceQuotient f z h 0#h =
  cong (_／ℂ[ h , 0#h ])
    (negDifferenceNumerator f z h)
  ∙ negDivide (f (z +ℂ h) -ℂ f z) h 0#h


negDerivativeError :
  ∀ f derivative z h (0#h : 0ℂ #ℂ h) →
  DifferenceQuotient (negateComplexFunction f) z h 0#h
    -ℂ (-ℂ derivative) ≡
  -ℂ (DifferenceQuotient f z h 0#h -ℂ derivative)
negDerivativeError f derivative z h 0#h =
  cong (_-ℂ (-ℂ derivative))
    (negDifferenceQuotient f z h 0#h)
  ∙ negDifferencePath (DifferenceQuotient f z h 0#h) derivative


negDerivativeErrorModulus :
  ∀ f derivative z h (0#h : 0ℂ #ℂ h) →
  modulus
    (DifferenceQuotient (negateComplexFunction f) z h 0#h
      -ℂ (-ℂ derivative)) ≡
  modulus (DifferenceQuotient f z h 0#h -ℂ derivative)
negDerivativeErrorModulus f derivative z h 0#h =
  cong modulus (negDerivativeError f derivative z h 0#h)
  ∙ modulus-neg (DifferenceQuotient f z h 0#h -ℂ derivative)


hasComplexDerivativeWithinAt-neg :
  ∀ {P f derivative z} →
  HasComplexDerivativeWithinAt P f derivative z →
  HasComplexDerivativeWithinAt P
    (negateComplexFunction f) (-ℂ derivative) z
hasComplexDerivativeWithinAt-neg
  {P} {f} {derivative} {z} derivativeAt ε =
  map-snd
    (λ estimate h 0#h z+h∈P |h|<δ →
      subst (_<ᵣ rat (fst ε))
        (sym (negDerivativeErrorModulus
          f derivative z h 0#h))
        (estimate h 0#h z+h∈P |h|<δ))
    (derivativeAt ε)


complexDifferentiableWithinAt-neg :
  ∀ {P f z} →
  ComplexDifferentiableWithinAt P f z →
  ComplexDifferentiableWithinAt P (negateComplexFunction f) z
complexDifferentiableWithinAt-neg
  {P} {f} {z} differentiable =
  -ℂ fst differentiable ,
  hasComplexDerivativeWithinAt-neg
    {P = P} {f = f} {derivative = fst differentiable} {z = z}
    (snd differentiable)


holomorphicOn-neg :
  ∀ {P f} →
  HolomorphicOn P f →
  HolomorphicOn P (negateComplexFunction f)
holomorphicOn-neg {P} {f} holomorphic z z∈P =
  complexDifferentiableWithinAt-neg
    {P = P} {f = f} {z = z}
    (holomorphic z z∈P)
