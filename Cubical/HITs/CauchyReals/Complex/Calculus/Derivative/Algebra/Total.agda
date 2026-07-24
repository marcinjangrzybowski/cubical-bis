module Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Total where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Bounds
open import Cubical.HITs.CauchyReals.Complex.Domain
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Within
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Addition
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Negation
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Subtraction
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Scaling
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Product
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Composition
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.NaturalPower
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Polynomial


hasComplexDerivativeAt-add :
  ∀ {f derivativeF g derivativeG z} →
  HasComplexDerivativeAt f derivativeF z →
  HasComplexDerivativeAt g derivativeG z →
  HasComplexDerivativeAt
    (addComplexFunctions f g) (derivativeF +ℂ derivativeG) z
hasComplexDerivativeAt-add
  {f} {derivativeF} {g} {derivativeG} {z}
  derivativeFAt derivativeGAt =
  let
    derivativeFWithin :
      HasComplexDerivativeWithinAt wholeℂ f derivativeF z
    derivativeFWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = f} {derivative = derivativeF} {z = z}
        derivativeFAt

    derivativeGWithin :
      HasComplexDerivativeWithinAt wholeℂ g derivativeG z
    derivativeGWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = g} {derivative = derivativeG} {z = z}
        derivativeGAt

    sumDerivativeWithin :
      HasComplexDerivativeWithinAt wholeℂ
        (addComplexFunctions f g) (derivativeF +ℂ derivativeG) z
    sumDerivativeWithin =
      hasComplexDerivativeWithinAt-add
        {P = wholeℂ} {f = f} {derivativeF = derivativeF}
        {g = g} {derivativeG = derivativeG} {z = z}
        derivativeFWithin derivativeGWithin
  in
  hasComplexDerivativeWithinWholeAt→At
    {f = addComplexFunctions f g}
    {derivative = derivativeF +ℂ derivativeG} {z = z}
    sumDerivativeWithin


hasComplexDerivativeAt-neg :
  ∀ {f derivative z} →
  HasComplexDerivativeAt f derivative z →
  HasComplexDerivativeAt
    (negateComplexFunction f) (-ℂ derivative) z
hasComplexDerivativeAt-neg {f} {derivative} {z} derivativeAt =
  let
    derivativeWithin :
      HasComplexDerivativeWithinAt wholeℂ f derivative z
    derivativeWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = f} {derivative = derivative} {z = z}
        derivativeAt

    negDerivativeWithin :
      HasComplexDerivativeWithinAt wholeℂ
        (negateComplexFunction f) (-ℂ derivative) z
    negDerivativeWithin =
      hasComplexDerivativeWithinAt-neg
        {P = wholeℂ} {f = f} {derivative = derivative} {z = z}
        derivativeWithin
  in
  hasComplexDerivativeWithinWholeAt→At
    {f = negateComplexFunction f}
    {derivative = -ℂ derivative} {z = z}
    negDerivativeWithin


hasComplexDerivativeAt-sub :
  ∀ {f derivativeF g derivativeG z} →
  HasComplexDerivativeAt f derivativeF z →
  HasComplexDerivativeAt g derivativeG z →
  HasComplexDerivativeAt
    (subtractComplexFunctions f g)
    (derivativeF +ℂ (-ℂ derivativeG)) z
hasComplexDerivativeAt-sub
  {f} {derivativeF} {g} {derivativeG} {z}
  derivativeFAt derivativeGAt =
  let
    derivativeFWithin :
      HasComplexDerivativeWithinAt wholeℂ f derivativeF z
    derivativeFWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = f} {derivative = derivativeF} {z = z}
        derivativeFAt

    derivativeGWithin :
      HasComplexDerivativeWithinAt wholeℂ g derivativeG z
    derivativeGWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = g} {derivative = derivativeG} {z = z}
        derivativeGAt

    subDerivativeWithin :
      HasComplexDerivativeWithinAt wholeℂ
        (subtractComplexFunctions f g)
        (derivativeF +ℂ (-ℂ derivativeG)) z
    subDerivativeWithin =
      hasComplexDerivativeWithinAt-sub
        {P = wholeℂ} {f = f} {derivativeF = derivativeF}
        {g = g} {derivativeG = derivativeG} {z = z}
        derivativeFWithin derivativeGWithin
  in
  hasComplexDerivativeWithinWholeAt→At
    {f = subtractComplexFunctions f g}
    {derivative = derivativeF +ℂ (-ℂ derivativeG)} {z = z}
    subDerivativeWithin


hasComplexDerivativeAt-scale :
  ∀ {c f derivative z} →
  ComplexScalarBound c →
  HasComplexDerivativeAt f derivative z →
  HasComplexDerivativeAt
    (scaleComplexFunction c f) (c ·ℂ derivative) z
hasComplexDerivativeAt-scale
  {c} {f} {derivative} {z} bound derivativeAt =
  let
    derivativeWithin :
      HasComplexDerivativeWithinAt wholeℂ f derivative z
    derivativeWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = f} {derivative = derivative} {z = z}
        derivativeAt

    scaledDerivativeWithin :
      HasComplexDerivativeWithinAt wholeℂ
        (scaleComplexFunction c f) (c ·ℂ derivative) z
    scaledDerivativeWithin =
      hasComplexDerivativeWithinAt-scale
        {P = wholeℂ} {c = c} {f = f}
        {derivative = derivative} {z = z}
        bound derivativeWithin
  in
  hasComplexDerivativeWithinWholeAt→At
    {f = scaleComplexFunction c f}
    {derivative = c ·ℂ derivative} {z = z}
    scaledDerivativeWithin


hasComplexDerivativeAt-mul :
  ∀ {f derivativeF g derivativeG z} →
  ComplexScalarBound (f z) →
  ComplexScalarBound derivativeF →
  ComplexScalarBound (g z) →
  ComplexScalarBound derivativeG →
  HasComplexDerivativeAt f derivativeF z →
  HasComplexDerivativeAt g derivativeG z →
  HasComplexDerivativeAt
    (multiplyComplexFunctions f g)
    (derivativeF ·ℂ g z +ℂ f z ·ℂ derivativeG) z
hasComplexDerivativeAt-mul
  {f} {derivativeF} {g} {derivativeG} {z}
  valueBoundF derivativeBoundF valueBoundG derivativeBoundG
  derivativeFAt derivativeGAt =
  let
    derivativeFWithin :
      HasComplexDerivativeWithinAt wholeℂ f derivativeF z
    derivativeFWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = f} {derivative = derivativeF} {z = z}
        derivativeFAt

    derivativeGWithin :
      HasComplexDerivativeWithinAt wholeℂ g derivativeG z
    derivativeGWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = g} {derivative = derivativeG} {z = z}
        derivativeGAt

    productDerivativeWithin :
      HasComplexDerivativeWithinAt wholeℂ
        (multiplyComplexFunctions f g)
        (derivativeF ·ℂ g z +ℂ f z ·ℂ derivativeG) z
    productDerivativeWithin =
      hasComplexDerivativeWithinAt-mul
        {P = wholeℂ}
        {f = f} {derivativeF = derivativeF}
        {g = g} {derivativeG = derivativeG} {z = z}
        valueBoundF derivativeBoundF
        valueBoundG derivativeBoundG
        derivativeFWithin derivativeGWithin
  in
  hasComplexDerivativeWithinWholeAt→At
    {f = multiplyComplexFunctions f g}
    {derivative =
      derivativeF ·ℂ g z +ℂ f z ·ℂ derivativeG}
    {z = z}
    productDerivativeWithin


complexDifferentiableAt-add :
  ∀ {f g z} →
  ComplexDifferentiableAt f z →
  ComplexDifferentiableAt g z →
  ComplexDifferentiableAt (addComplexFunctions f g) z
complexDifferentiableAt-add
  {f} {g} {z} differentiableF differentiableG =
  fst differentiableF +ℂ fst differentiableG ,
  hasComplexDerivativeAt-add
    {f = f} {derivativeF = fst differentiableF}
    {g = g} {derivativeG = fst differentiableG} {z = z}
    (snd differentiableF) (snd differentiableG)


complexDifferentiableAt-neg :
  ∀ {f z} →
  ComplexDifferentiableAt f z →
  ComplexDifferentiableAt (negateComplexFunction f) z
complexDifferentiableAt-neg {f} {z} differentiable =
  -ℂ fst differentiable ,
  hasComplexDerivativeAt-neg
    {f = f} {derivative = fst differentiable} {z = z}
    (snd differentiable)


complexDifferentiableAt-sub :
  ∀ {f g z} →
  ComplexDifferentiableAt f z →
  ComplexDifferentiableAt g z →
  ComplexDifferentiableAt (subtractComplexFunctions f g) z
complexDifferentiableAt-sub
  {f} {g} {z} differentiableF differentiableG =
  fst differentiableF +ℂ (-ℂ fst differentiableG) ,
  hasComplexDerivativeAt-sub
    {f = f} {derivativeF = fst differentiableF}
    {g = g} {derivativeG = fst differentiableG} {z = z}
    (snd differentiableF) (snd differentiableG)


complexDifferentiableAt-scale :
  ∀ {c f z} →
  ComplexScalarBound c →
  ComplexDifferentiableAt f z →
  ComplexDifferentiableAt (scaleComplexFunction c f) z
complexDifferentiableAt-scale
  {c} {f} {z} bound differentiable =
  c ·ℂ fst differentiable ,
  hasComplexDerivativeAt-scale
    {c = c} {f = f}
    {derivative = fst differentiable} {z = z}
    bound (snd differentiable)


complexDifferentiableAt-mul :
  ∀ {f g z}
  (differentiableF : ComplexDifferentiableAt f z)
  (differentiableG : ComplexDifferentiableAt g z) →
  ComplexScalarBound (f z) →
  ComplexScalarBound (fst differentiableF) →
  ComplexScalarBound (g z) →
  ComplexScalarBound (fst differentiableG) →
  ComplexDifferentiableAt (multiplyComplexFunctions f g) z
complexDifferentiableAt-mul
  {f} {g} {z} differentiableF differentiableG
  valueBoundF derivativeBoundF valueBoundG derivativeBoundG =
  (fst differentiableF ·ℂ g z
    +ℂ f z ·ℂ fst differentiableG) ,
  hasComplexDerivativeAt-mul
    {f = f} {derivativeF = fst differentiableF}
    {g = g} {derivativeG = fst differentiableG} {z = z}
    valueBoundF derivativeBoundF
    valueBoundG derivativeBoundG
    (snd differentiableF) (snd differentiableG)


holomorphic-add :
  ∀ {f g} →
  Holomorphic f → Holomorphic g →
  Holomorphic (addComplexFunctions f g)
holomorphic-add {f} {g} holomorphicF holomorphicG z =
  complexDifferentiableAt-add
    {f = f} {g = g} {z = z}
    (holomorphicF z) (holomorphicG z)


holomorphic-neg :
  ∀ {f} → Holomorphic f → Holomorphic (negateComplexFunction f)
holomorphic-neg {f} holomorphic z =
  complexDifferentiableAt-neg
    {f = f} {z = z} (holomorphic z)


holomorphic-sub :
  ∀ {f g} →
  Holomorphic f → Holomorphic g →
  Holomorphic (subtractComplexFunctions f g)
holomorphic-sub {f} {g} holomorphicF holomorphicG z =
  complexDifferentiableAt-sub
    {f = f} {g = g} {z = z}
    (holomorphicF z) (holomorphicG z)


holomorphic-scale :
  ∀ {c f} →
  ComplexScalarBound c →
  Holomorphic f →
  Holomorphic (scaleComplexFunction c f)
holomorphic-scale {c} {f} bound holomorphic z =
  complexDifferentiableAt-scale
    {c = c} {f = f} {z = z}
    bound (holomorphic z)


holomorphic-mul :
  ∀ {f g}
  (holomorphicF : Holomorphic f)
  (holomorphicG : Holomorphic g) →
  ((z : ℂ) → ComplexScalarBound (f z)) →
  ((z : ℂ) →
    ComplexScalarBound (fst (holomorphicF z))) →
  ((z : ℂ) → ComplexScalarBound (g z)) →
  ((z : ℂ) →
    ComplexScalarBound (fst (holomorphicG z))) →
  Holomorphic (multiplyComplexFunctions f g)
holomorphic-mul
  {f} {g} holomorphicF holomorphicG
  valueBoundF derivativeBoundF
  valueBoundG derivativeBoundG z =
  complexDifferentiableAt-mul
    {f = f} {g = g} {z = z}
    (holomorphicF z) (holomorphicG z)
    (valueBoundF z) (derivativeBoundF z)
    (valueBoundG z) (derivativeBoundG z)


hasComplexDerivativeAt-compose :
  ∀ {g derivativeG f derivativeF z} →
  LocallyPreservesApartIncrementsAt f z →
  ComplexScalarBound derivativeF →
  ComplexScalarBound derivativeG →
  HasComplexDerivativeAt f derivativeF z →
  HasComplexDerivativeAt g derivativeG (f z) →
  HasComplexDerivativeAt
    (composeComplexFunctions g f)
    (derivativeG ·ℂ derivativeF) z
hasComplexDerivativeAt-compose
  {g} {derivativeG} {f} {derivativeF} {z}
  preservesApart derivativeBoundF derivativeBoundG
  derivativeFAt derivativeGAt =
  let
    derivativeFWithin :
      HasComplexDerivativeWithinAt
        wholeℂ f derivativeF z
    derivativeFWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = f} {derivative = derivativeF} {z = z}
        derivativeFAt

    derivativeGWithin :
      HasComplexDerivativeWithinAt
        wholeℂ g derivativeG (f z)
    derivativeGWithin =
      hasComplexDerivativeAt→Within wholeℂ
        {f = g} {derivative = derivativeG} {z = f z}
        derivativeGAt

    compositionDerivativeWithin :
      HasComplexDerivativeWithinAt wholeℂ
        (composeComplexFunctions g f)
        (derivativeG ·ℂ derivativeF) z
    compositionDerivativeWithin =
      hasComplexDerivativeWithinAt-compose
        {P = wholeℂ} {Q = wholeℂ}
        {g = g} {derivativeG = derivativeG}
        {f = f} {derivativeF = derivativeF} {z = z}
        (λ _ _ → tt)
        (locallyPreservesApartIncrementsAt→Within
          wholeℂ {f = f} {z = z} preservesApart)
        derivativeBoundF derivativeBoundG
        derivativeFWithin derivativeGWithin
  in
  hasComplexDerivativeWithinWholeAt→At
    {f = composeComplexFunctions g f}
    {derivative = derivativeG ·ℂ derivativeF}
    {z = z}
    compositionDerivativeWithin


complexDifferentiableAt-compose :
  ∀ {g f z}
  (preservesApart :
    LocallyPreservesApartIncrementsAt f z)
  (differentiableF :
    ComplexDifferentiableAt f z)
  (differentiableG :
    ComplexDifferentiableAt g (f z)) →
  ComplexScalarBound (fst differentiableF) →
  ComplexScalarBound (fst differentiableG) →
  ComplexDifferentiableAt
    (composeComplexFunctions g f) z
complexDifferentiableAt-compose
  {g} {f} {z} preservesApart
  differentiableF differentiableG
  derivativeBoundF derivativeBoundG =
  fst differentiableG ·ℂ fst differentiableF ,
  hasComplexDerivativeAt-compose
    {g = g} {derivativeG = fst differentiableG}
    {f = f} {derivativeF = fst differentiableF}
    {z = z}
    preservesApart
    derivativeBoundF derivativeBoundG
    (snd differentiableF) (snd differentiableG)


holomorphic-compose :
  ∀ {g f}
  (preservesApart :
    (z : ℂ) → LocallyPreservesApartIncrementsAt f z)
  (holomorphicF : Holomorphic f)
  (holomorphicG : Holomorphic g) →
  ((z : ℂ) →
    ComplexScalarBound (fst (holomorphicF z))) →
  ((z : ℂ) →
    ComplexScalarBound (fst (holomorphicG (f z)))) →
  Holomorphic (composeComplexFunctions g f)
holomorphic-compose
  {g} {f} preservesApart
  holomorphicF holomorphicG
  derivativeBoundF derivativeBoundG z =
  complexDifferentiableAt-compose
    {g = g} {f = f} {z = z}
    (preservesApart z)
    (holomorphicF z) (holomorphicG (f z))
    (derivativeBoundF z) (derivativeBoundG z)


hasComplexDerivativeAt-naturalPower-zero :
  ∀ z →
  HasComplexDerivativeAt
    (naturalPowerComplexFunction zero)
    0ℂ z
hasComplexDerivativeAt-naturalPower-zero z =
  hasComplexDerivativeWithinWholeAt→At
    {f = naturalPowerComplexFunction zero}
    {derivative = 0ℂ}
    {z = z}
    (hasComplexDerivativeWithinAt-naturalPower-zero
      wholeℂ z)


hasComplexDerivativeAt-positiveNaturalPower :
  ∀ n z →
  ComplexScalarBound z →
  HasComplexDerivativeAt
    (naturalPowerComplexFunction (suc n))
    (positiveNaturalComplex n
      ·ℂ naturalPowerComplexFunction n z)
    z
hasComplexDerivativeAt-positiveNaturalPower
  n z bound =
  hasComplexDerivativeWithinWholeAt→At
    {f = naturalPowerComplexFunction (suc n)}
    {derivative =
      positiveNaturalComplex n
        ·ℂ naturalPowerComplexFunction n z}
    {z = z}
    (hasComplexDerivativeWithinAt-positiveNaturalPower
      wholeℂ n z bound)


complexDifferentiableAt-naturalPower :
  ∀ n z →
  ComplexScalarBound z →
  ComplexDifferentiableAt
    (naturalPowerComplexFunction n) z
complexDifferentiableAt-naturalPower n z bound =
  complexDifferentiableWithinWholeAt→At
    {f = naturalPowerComplexFunction n}
    {z = z}
    (complexDifferentiableWithinAt-naturalPower
      wholeℂ n z bound)


holomorphic-naturalPower :
  ∀ n →
  ((z : ℂ) → ComplexScalarBound z) →
  Holomorphic (naturalPowerComplexFunction n)
holomorphic-naturalPower n bound z =
  complexDifferentiableAt-naturalPower
    n z (bound z)


hasComplexDerivativeAt-polynomial :
  ∀ (coefficients : List ℂ) z →
  ComplexScalarBound z →
  PolynomialTailBoundsAt z coefficients →
  HasComplexDerivativeAt
    (evaluatePolynomial coefficients)
    (evaluatePolynomialDerivative coefficients z)
    z
hasComplexDerivativeAt-polynomial
  coefficients z zBound tailBounds =
  hasComplexDerivativeWithinWholeAt→At
    {f = evaluatePolynomial coefficients}
    {derivative =
      evaluatePolynomialDerivative coefficients z}
    {z = z}
    (hasComplexDerivativeWithinAt-polynomial
      wholeℂ coefficients z zBound tailBounds)


hasComplexDerivativeAt-linearPolynomial :
  ∀ a b z →
  ComplexScalarBound z →
  ComplexScalarBound a →
  HasComplexDerivativeAt
    (evaluatePolynomial (b ∷ a ∷ []))
    a z
hasComplexDerivativeAt-linearPolynomial
  a b z zBound aBound =
  hasComplexDerivativeWithinWholeAt→At
    {f = evaluatePolynomial (b ∷ a ∷ [])}
    {derivative = a}
    {z = z}
    (hasComplexDerivativeWithinAt-linearPolynomial
      wholeℂ a b z zBound aBound)


complexDifferentiableAt-polynomial :
  ∀ (coefficients : List ℂ) z →
  ComplexScalarBound z →
  PolynomialTailBoundsAt z coefficients →
  ComplexDifferentiableAt
    (evaluatePolynomial coefficients) z
complexDifferentiableAt-polynomial
  coefficients z zBound tailBounds =
  complexDifferentiableWithinWholeAt→At
    {f = evaluatePolynomial coefficients}
    {z = z}
    (complexDifferentiableWithinAt-polynomial
      wholeℂ coefficients z zBound tailBounds)


holomorphic-polynomial :
  ∀ (coefficients : List ℂ) →
  ((z : ℂ) → ComplexScalarBound z) →
  ((z : ℂ) →
    PolynomialTailBoundsAt z coefficients) →
  Holomorphic (evaluatePolynomial coefficients)
holomorphic-polynomial
  coefficients zBound tailBounds z =
  complexDifferentiableAt-polynomial
    coefficients z
    (zBound z)
    (tailBounds z)
