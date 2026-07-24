module Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Scaling where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Inverse as ℚ using (_⁻¹₊ ; y·[x/y])
open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Inverse.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.Bounds
open import Cubical.HITs.CauchyReals.Complex.Domain
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Within

scaleComplexFunction : ℂ → (ℂ → ℂ) → ℂ → ℂ
scaleComplexFunction c f z = c ·ℂ f z


scaleDifferencePath : ∀ c x y →
  (c ·ℂ x) -ℂ (c ·ℂ y) ≡ c ·ℂ (x -ℂ y)
scaleDifferencePath c x y =
  sym (Cℂ.·DistR- c x y)


scaleDifferenceNumerator :
  ∀ c f z h →
  scaleComplexFunction c f (z +ℂ h)
    -ℂ scaleComplexFunction c f z ≡
  c ·ℂ (f (z +ℂ h) -ℂ f z)
scaleDifferenceNumerator c f z h =
  scaleDifferencePath c (f (z +ℂ h)) (f z)


scaleDivide :
  ∀ c x h (0#h : 0ℂ #ℂ h) →
  (c ·ℂ x) ／ℂ[ h , 0#h ] ≡
  c ·ℂ (x ／ℂ[ h , 0#h ])
scaleDivide c x h 0#h =
  sym (·ℂAssoc c x (invℂ h 0#h))


scaleDifferenceQuotient :
  ∀ c f z h (0#h : 0ℂ #ℂ h) →
  DifferenceQuotient (scaleComplexFunction c f) z h 0#h ≡
  c ·ℂ DifferenceQuotient f z h 0#h
scaleDifferenceQuotient c f z h 0#h =
  cong (_／ℂ[ h , 0#h ])
    (scaleDifferenceNumerator c f z h)
  ∙ scaleDivide c (f (z +ℂ h) -ℂ f z) h 0#h


scaleDerivativeError :
  ∀ c f derivative z h (0#h : 0ℂ #ℂ h) →
  DifferenceQuotient (scaleComplexFunction c f) z h 0#h
    -ℂ (c ·ℂ derivative) ≡
  c ·ℂ
    (DifferenceQuotient f z h 0#h -ℂ derivative)
scaleDerivativeError c f derivative z h 0#h =
  cong (_-ℂ (c ·ℂ derivative))
    (scaleDifferenceQuotient c f z h 0#h)
  ∙ scaleDifferencePath
      c (DifferenceQuotient f z h 0#h) derivative


scaleDerivativeErrorModulus :
  ∀ c f derivative z h (0#h : 0ℂ #ℂ h) →
  modulus
    (DifferenceQuotient (scaleComplexFunction c f) z h 0#h
      -ℂ (c ·ℂ derivative)) ≡
  modulus c ·ᵣ
    modulus (DifferenceQuotient f z h 0#h -ℂ derivative)
scaleDerivativeErrorModulus c f derivative z h 0#h =
  cong modulus
    (scaleDerivativeError c f derivative z h 0#h)
  ∙ modulus-mul c
      (DifferenceQuotient f z h 0#h -ℂ derivative)

hasComplexDerivativeWithinAt-scale :
  ∀ {P c f derivative z} →
  ComplexScalarBound c →
  HasComplexDerivativeWithinAt P f derivative z →
  HasComplexDerivativeWithinAt P
    (scaleComplexFunction c f) (c ·ℂ derivative) z
hasComplexDerivativeWithinAt-scale
  {P} {c} {f} {derivative} {z}
  (M , |c|≤M) derivativeAt ε =
  let
    η : ℚ₊
    η = (ℚ._⁻¹₊ M) ·₊ ε

    δ , estimate = derivativeAt η
  in
  δ ,
  λ h 0#h z+h∈P |h|<δ →
    subst (_<ᵣ rat (fst ε))
      (sym
        (scaleDerivativeErrorModulus
          c f derivative z h 0#h))
      (boundedModulusProduct<
        c
        (DifferenceQuotient f z h 0#h -ℂ derivative)
        M ε |c|≤M
        (estimate h 0#h z+h∈P |h|<δ))


complexDifferentiableWithinAt-scale :
  ∀ {P c f z} →
  ComplexScalarBound c →
  ComplexDifferentiableWithinAt P f z →
  ComplexDifferentiableWithinAt P (scaleComplexFunction c f) z
complexDifferentiableWithinAt-scale
  {P} {c} {f} {z} bound differentiable =
  c ·ℂ fst differentiable ,
  hasComplexDerivativeWithinAt-scale
    {P = P} {c = c} {f = f}
    {derivative = fst differentiable} {z = z}
    bound (snd differentiable)


holomorphicOn-scale :
  ∀ {P c f} →
  ComplexScalarBound c →
  HolomorphicOn P f →
  HolomorphicOn P (scaleComplexFunction c f)
holomorphicOn-scale
  {P} {c} {f} bound holomorphic z z∈P =
  complexDifferentiableWithinAt-scale
    {P = P} {c = c} {f = f} {z = z}
    bound (holomorphic z z∈P)
