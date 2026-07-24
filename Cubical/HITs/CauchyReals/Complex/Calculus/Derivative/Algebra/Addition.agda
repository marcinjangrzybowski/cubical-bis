module Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Inverse.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality
open import Cubical.HITs.CauchyReals.Complex.Domain
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Within

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


addComplexFunctions : (ℂ → ℂ) → (ℂ → ℂ) → ℂ → ℂ
addComplexFunctions f g z = f z +ℂ g z


addDifferenceNumerator :
  ∀ f g z h →
  addComplexFunctions f g (z +ℂ h)
    -ℂ addComplexFunctions f g z ≡
  (f (z +ℂ h) -ℂ f z)
    +ℂ
  (g (z +ℂ h) -ℂ g z)
addDifferenceNumerator f g z h =
  ℂ≡ ℝ! ℝ!


addDivide :
  ∀ x y h (0#h : 0ℂ #ℂ h) →
  (x +ℂ y) ／ℂ[ h , 0#h ] ≡
  (x ／ℂ[ h , 0#h ]) +ℂ (y ／ℂ[ h , 0#h ])
addDivide x y h 0#h =
  Cℂ.·DistL+ x y (invℂ h 0#h)


addDifferenceQuotient :
  ∀ f g z h (0#h : 0ℂ #ℂ h) →
  DifferenceQuotient (addComplexFunctions f g) z h 0#h ≡
  DifferenceQuotient f z h 0#h +ℂ
  DifferenceQuotient g z h 0#h
addDifferenceQuotient f g z h 0#h =
  cong (_／ℂ[ h , 0#h ])
    (addDifferenceNumerator f g z h)
  ∙ addDivide
      (f (z +ℂ h) -ℂ f z)
      (g (z +ℂ h) -ℂ g z)
      h 0#h


addErrorPath : ∀ x derivativeX y derivativeY →
  (x +ℂ y) -ℂ (derivativeX +ℂ derivativeY) ≡
  (x -ℂ derivativeX) +ℂ (y -ℂ derivativeY)
addErrorPath x derivativeX y derivativeY =
  ℂ≡ ℝ! ℝ!


addDerivativeError :
  ∀ f derivativeF g derivativeG z h (0#h : 0ℂ #ℂ h) →
  DifferenceQuotient (addComplexFunctions f g) z h 0#h
    -ℂ (derivativeF +ℂ derivativeG) ≡
  (DifferenceQuotient f z h 0#h -ℂ derivativeF)
    +ℂ
  (DifferenceQuotient g z h 0#h -ℂ derivativeG)
addDerivativeError f derivativeF g derivativeG z h 0#h =
  cong (_-ℂ (derivativeF +ℂ derivativeG))
    (addDifferenceQuotient f g z h 0#h)
  ∙ addErrorPath
      (DifferenceQuotient f z h 0#h) derivativeF
      (DifferenceQuotient g z h 0#h) derivativeG


modulusSumOfHalves< :
  ∀ ε u v →
  modulus u <ᵣ rat (fst (ε /2₊)) →
  modulus v <ᵣ rat (fst (ε /2₊)) →
  modulus (u +ℂ v) <ᵣ rat (fst ε)
modulusSumOfHalves< ε u v |u|<ε/2 |v|<ε/2 =
  isTrans≤<ᵣ _ _ _
    (modulus-triangle u v)
    (isTrans<≡ᵣ _ _ _
      (<ᵣMonotone+ᵣ _ _ _ _ |u|<ε/2 |v|<ε/2)
      (+ᵣ-rat _ _
      ∙ cong rat (1/2∈ℚ./2+/2≡id (fst ε))))


modulus<min→left :
  ∀ h δ η →
  modulus h <ᵣ rat (fst (min₊ δ η)) →
  modulus h <ᵣ rat (fst δ)
modulus<min→left h δ η |h|<min =
  isTrans<≤ᵣ _ _ _ |h|<min
    (≤ℚ→≤ᵣ _ _ (ℚ.min≤ (fst δ) (fst η)))


modulus<min→right :
  ∀ h δ η →
  modulus h <ᵣ rat (fst (min₊ δ η)) →
  modulus h <ᵣ rat (fst η)
modulus<min→right h δ η |h|<min =
  isTrans<≤ᵣ _ _ _ |h|<min
    (≤ℚ→≤ᵣ _ _ (ℚ.min≤' (fst δ) (fst η)))


hasComplexDerivativeWithinAt-add :
  ∀ {P f derivativeF g derivativeG z} →
  HasComplexDerivativeWithinAt P f derivativeF z →
  HasComplexDerivativeWithinAt P g derivativeG z →
  HasComplexDerivativeWithinAt P
    (addComplexFunctions f g) (derivativeF +ℂ derivativeG) z
hasComplexDerivativeWithinAt-add
  {P} {f} {derivativeF} {g} {derivativeG} {z}
  derivativeFAt derivativeGAt ε =
  let
    δ , estimateF = derivativeFAt (ε /2₊)
    η , estimateG = derivativeGAt (ε /2₊)
  in
  min₊ δ η ,
  λ h 0#h z+h∈P |h|<min →
    subst (_<ᵣ rat (fst ε))
      (sym (cong modulus
        (addDerivativeError
          f derivativeF g derivativeG z h 0#h)))
      (modulusSumOfHalves< ε
        (DifferenceQuotient f z h 0#h -ℂ derivativeF)
        (DifferenceQuotient g z h 0#h -ℂ derivativeG)
        (estimateF h 0#h z+h∈P
          (modulus<min→left h δ η |h|<min))
        (estimateG h 0#h z+h∈P
          (modulus<min→right h δ η |h|<min)))


complexDifferentiableWithinAt-add :
  ∀ {P f g z} →
  ComplexDifferentiableWithinAt P f z →
  ComplexDifferentiableWithinAt P g z →
  ComplexDifferentiableWithinAt P (addComplexFunctions f g) z
complexDifferentiableWithinAt-add
  {P} {f} {g} {z} differentiableF differentiableG =
  fst differentiableF +ℂ fst differentiableG ,
  hasComplexDerivativeWithinAt-add
    {P = P} {f = f} {derivativeF = fst differentiableF}
    {g = g} {derivativeG = fst differentiableG} {z = z}
    (snd differentiableF) (snd differentiableG)


holomorphicOn-add :
  ∀ {P f g} →
  HolomorphicOn P f → HolomorphicOn P g →
  HolomorphicOn P (addComplexFunctions f g)
holomorphicOn-add {P} {f} {g} holomorphicF holomorphicG z z∈P =
  complexDifferentiableWithinAt-add
    {P = P} {f = f} {g = g} {z = z}
    (holomorphicF z z∈P) (holomorphicG z z∈P)
