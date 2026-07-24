module Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Composition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Inverse as ℚ using (_⁻¹₊)
open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Inverse.Definition
open import Cubical.HITs.CauchyReals.Complex.Inverse.Cancellation
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.Bounds
open import Cubical.HITs.CauchyReals.Complex.Domain
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Within
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Addition
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Product

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


composeComplexFunctions :
  (ℂ → ℂ) → (ℂ → ℂ) → ℂ → ℂ
composeComplexFunctions g f z = g (f z)


MapsComplexPredicates :
  (ℂ → ℂ) → ComplexPredicate → ComplexPredicate → Type₀
MapsComplexPredicates f P Q =
  (z : ℂ) → z ∈ P → f z ∈ Q


innerIncrement :
  (ℂ → ℂ) → ℂ → ℂ → ℂ
innerIncrement f z h =
  f (z +ℂ h) -ℂ f z


PreservesApartIncrementsWithinAt :
  ComplexPredicate → (ℂ → ℂ) → ℂ → Type₀
PreservesApartIncrementsWithinAt P f z =
  (h : ℂ) → 0ℂ #ℂ h → z +ℂ h ∈ P →
  0ℂ #ℂ innerIncrement f z h


LocallyPreservesApartIncrementsWithinAt :
  ComplexPredicate → (ℂ → ℂ) → ℂ → Type₀
LocallyPreservesApartIncrementsWithinAt P f z =
  Σ[ radius ∈ ℚ₊ ]
    ((h : ℂ) → 0ℂ #ℂ h → z +ℂ h ∈ P →
      modulus h <ᵣ rat (fst radius) →
      0ℂ #ℂ innerIncrement f z h)


preservesApartIncrementsWithinAt→Locally :
  ∀ P {f z} →
  PreservesApartIncrementsWithinAt P f z →
  LocallyPreservesApartIncrementsWithinAt P f z
preservesApartIncrementsWithinAt→Locally
  P preserves =
  oneℚ₊ ,
  λ h 0#h z+h∈P _ →
    preserves h 0#h z+h∈P


PreservesApartIncrementsAt :
  (ℂ → ℂ) → ℂ → Type₀
PreservesApartIncrementsAt f z =
  (h : ℂ) → 0ℂ #ℂ h →
  0ℂ #ℂ innerIncrement f z h


LocallyPreservesApartIncrementsAt :
  (ℂ → ℂ) → ℂ → Type₀
LocallyPreservesApartIncrementsAt f z =
  Σ[ radius ∈ ℚ₊ ]
    ((h : ℂ) → 0ℂ #ℂ h →
      modulus h <ᵣ rat (fst radius) →
      0ℂ #ℂ innerIncrement f z h)


preservesApartIncrementsAt→Locally :
  ∀ {f z} →
  PreservesApartIncrementsAt f z →
  LocallyPreservesApartIncrementsAt f z
preservesApartIncrementsAt→Locally preserves =
  oneℚ₊ ,
  λ h 0#h _ → preserves h 0#h


locallyPreservesApartIncrementsAt→Within :
  ∀ P {f z} →
  LocallyPreservesApartIncrementsAt f z →
  LocallyPreservesApartIncrementsWithinAt P f z
locallyPreservesApartIncrementsAt→Within
  P (radius , preserves) =
  radius ,
  λ h 0#h _ |h|<radius →
    preserves h 0#h |h|<radius


composeDifferenceNumerator :
  ∀ g f z h →
  composeComplexFunctions g f (z +ℂ h)
    -ℂ composeComplexFunctions g f z ≡
  g (f z +ℂ innerIncrement f z h) -ℂ g (f z)
composeDifferenceNumerator g f z h =
  cong (λ value → g value -ℂ g (f z))
    (differenceReconstructPath
      (f (z +ℂ h)) (f z))


fourFactorReorder : ∀ x u k v →
  (x ·ℂ u) ·ℂ (k ·ℂ v) ≡
  (u ·ℂ k) ·ℂ (x ·ℂ v)
fourFactorReorder x u k v =
  ℂ≡ ℝ! ℝ!


divideThroughIncrement :
  ∀ x h k
  (0#h : 0ℂ #ℂ h)
  (0#k : 0ℂ #ℂ k) →
  x ／ℂ[ h , 0#h ] ≡
  (x ／ℂ[ k , 0#k ]) ·ℂ
  (k ／ℂ[ h , 0#h ])
divideThroughIncrement x h k 0#h 0#k =
  sym
    (fourFactorReorder
      x (invℂ k 0#k) k (invℂ h 0#h)
    ∙ cong
        (λ factor →
          factor ·ℂ (x ·ℂ invℂ h 0#h))
        (invℂ· k 0#k)
    ∙ ·ℂComm 1ℂ (x ·ℂ invℂ h 0#h)
    ∙ ·ℂIdR (x ·ℂ invℂ h 0#h))


composeDifferenceQuotient :
  ∀ g f z h
  (0#h : 0ℂ #ℂ h)
  (0#inner :
    0ℂ #ℂ innerIncrement f z h) →
  DifferenceQuotient
    (composeComplexFunctions g f) z h 0#h ≡
  DifferenceQuotient
    g (f z) (innerIncrement f z h) 0#inner
    ·ℂ
  DifferenceQuotient f z h 0#h
composeDifferenceQuotient
  g f z h 0#h 0#inner =
  cong (_／ℂ[ h , 0#h ])
    (composeDifferenceNumerator g f z h)
  ∙ divideThroughIncrement
      (g (f z +ℂ innerIncrement f z h) -ℂ g (f z))
      h (innerIncrement f z h)
      0#h 0#inner


composeDerivativeErrorPath :
  ∀ quotientG quotientF derivativeG derivativeF →
  quotientG ·ℂ quotientF
    -ℂ derivativeG ·ℂ derivativeF ≡
  quotientF ·ℂ (quotientG -ℂ derivativeG)
    +ℂ
  derivativeG ·ℂ (quotientF -ℂ derivativeF)
composeDerivativeErrorPath
  quotientG quotientF derivativeG derivativeF =
  ℂ≡ ℝ! ℝ!


composeDerivativeError :
  ∀ g derivativeG f derivativeF z h
  (0#h : 0ℂ #ℂ h)
  (0#inner :
    0ℂ #ℂ innerIncrement f z h) →
  DifferenceQuotient
    (composeComplexFunctions g f) z h 0#h
    -ℂ derivativeG ·ℂ derivativeF ≡
  DifferenceQuotient f z h 0#h
    ·ℂ
  (DifferenceQuotient
    g (f z) (innerIncrement f z h) 0#inner
    -ℂ derivativeG)
    +ℂ
  derivativeG ·ℂ
    (DifferenceQuotient f z h 0#h -ℂ derivativeF)
composeDerivativeError
  g derivativeG f derivativeF z h 0#h 0#inner =
  cong (_-ℂ (derivativeG ·ℂ derivativeF))
    (composeDifferenceQuotient
      g f z h 0#h 0#inner)
  ∙ composeDerivativeErrorPath
      (DifferenceQuotient
        g (f z) (innerIncrement f z h) 0#inner)
      (DifferenceQuotient f z h 0#h)
      derivativeG derivativeF


innerIncrementAsQuotientProduct :
  ∀ f z h (0#h : 0ℂ #ℂ h) →
  innerIncrement f z h ≡
  DifferenceQuotient f z h 0#h ·ℂ h
innerIncrementAsQuotientProduct f z h 0#h =
  divideReconstruct
    (innerIncrement f z h) h 0#h
  ∙ ·ℂComm h (DifferenceQuotient f z h 0#h)


innerIncrementModulus< :
  ∀ f z h (0#h : 0ℂ #ℂ h) (M radius : ℚ₊) →
  modulus (DifferenceQuotient f z h 0#h)
    ≤ᵣ rat (fst M) →
  modulus h
    <ᵣ rat (fst ((ℚ._⁻¹₊ M) ·₊ radius)) →
  modulus (innerIncrement f z h)
    <ᵣ rat (fst radius)
innerIncrementModulus<
  f z h 0#h M radius |quotient|≤M |h|<scaledRadius =
  isTrans≡<ᵣ _ _ _
    (cong modulus
      (innerIncrementAsQuotientProduct f z h 0#h))
    (boundedComplexProductModulus<
      (DifferenceQuotient f z h 0#h)
      h M radius |quotient|≤M |h|<scaledRadius)


hasComplexDerivativeWithinAt-compose :
  ∀ {P Q g derivativeG f derivativeF z} →
  MapsComplexPredicates f P Q →
  LocallyPreservesApartIncrementsWithinAt P f z →
  ComplexScalarBound derivativeF →
  ComplexScalarBound derivativeG →
  HasComplexDerivativeWithinAt P f derivativeF z →
  HasComplexDerivativeWithinAt Q g derivativeG (f z) →
  HasComplexDerivativeWithinAt P
    (composeComplexFunctions g f)
    (derivativeG ·ℂ derivativeF) z
hasComplexDerivativeWithinAt-compose
  {P} {Q} {g} {derivativeG} {f} {derivativeF} {z}
  mapsInto (apartRadius , preservesApart)
  (derivativeBoundF , |derivativeF|≤derivativeBoundF)
  (derivativeBoundG , |derivativeG|≤derivativeBoundG)
  derivativeFAt derivativeGAt ε =
  let
    halfε : ℚ₊
    halfε = ε /2₊

    quotientBoundF : ℚ₊
    quotientBoundF =
      oneℚ₊ +₊ derivativeBoundF

    outerErrorTarget : ℚ₊
    outerErrorTarget =
      (ℚ._⁻¹₊ quotientBoundF) ·₊ halfε

    innerErrorTarget : ℚ₊
    innerErrorTarget =
      (ℚ._⁻¹₊ derivativeBoundG) ·₊ halfε

    innerDerivativeTolerance : ℚ₊
    innerDerivativeTolerance =
      min₊ innerErrorTarget oneℚ₊

    radiusF , estimateF =
      derivativeFAt innerDerivativeTolerance

    radiusG , estimateG =
      derivativeGAt outerErrorTarget

    innerRadius : ℚ₊
    innerRadius =
      (ℚ._⁻¹₊ quotientBoundF) ·₊ radiusG

    radius : ℚ₊
    radius =
      min₊ (min₊ radiusF innerRadius) apartRadius
  in
  radius ,
  λ h 0#h z+h∈P |h|<radius →
    let
      increment : ℂ
      increment =
        innerIncrement f z h

      |h|<apartRadius :
        modulus h <ᵣ rat (fst apartRadius)
      |h|<apartRadius =
        modulus<nestedMin→third
          h radiusF innerRadius apartRadius |h|<radius

      0#increment : 0ℂ #ℂ increment
      0#increment =
        preservesApart
          h 0#h z+h∈P |h|<apartRadius

      quotientF : ℂ
      quotientF =
        DifferenceQuotient f z h 0#h

      quotientG : ℂ
      quotientG =
        DifferenceQuotient
          g (f z) increment 0#increment

      errorF : ℂ
      errorF =
        quotientF -ℂ derivativeF

      errorG : ℂ
      errorG =
        quotientG -ℂ derivativeG

      |h|<radiusF :
        modulus h <ᵣ rat (fst radiusF)
      |h|<radiusF =
        modulus<nestedMin→first
          h radiusF innerRadius apartRadius |h|<radius

      |h|<innerRadius :
        modulus h <ᵣ rat (fst innerRadius)
      |h|<innerRadius =
        modulus<nestedMin→second
          h radiusF innerRadius apartRadius |h|<radius

      |errorF|<tolerance :
        modulus errorF
          <ᵣ rat (fst innerDerivativeTolerance)
      |errorF|<tolerance =
        estimateF h 0#h z+h∈P |h|<radiusF

      |errorF|<target :
        modulus errorF
          <ᵣ rat (fst innerErrorTarget)
      |errorF|<target =
        modulus<min→left
          errorF innerErrorTarget oneℚ₊
          |errorF|<tolerance

      |errorF|<1 :
        modulus errorF <ᵣ rat (fst oneℚ₊)
      |errorF|<1 =
        modulus<min→right
          errorF innerErrorTarget oneℚ₊
          |errorF|<tolerance

      |quotientF|≤bound :
        modulus quotientF
          ≤ᵣ rat (fst quotientBoundF)
      |quotientF|≤bound =
        quotientModulusBound
          quotientF derivativeF derivativeBoundF
          |derivativeF|≤derivativeBoundF
          |errorF|<1

      |increment|<radiusG :
        modulus increment <ᵣ rat (fst radiusG)
      |increment|<radiusG =
        innerIncrementModulus<
          f z h 0#h quotientBoundF radiusG
          |quotientF|≤bound |h|<innerRadius

      f[z+h]∈Q : f (z +ℂ h) ∈ Q
      f[z+h]∈Q =
        mapsInto (z +ℂ h) z+h∈P

      f[z]+increment∈Q :
        f z +ℂ increment ∈ Q
      f[z]+increment∈Q =
        subst (_∈ Q)
          (differenceReconstructPath
            (f (z +ℂ h)) (f z))
          f[z+h]∈Q

      |errorG|<target :
        modulus errorG
          <ᵣ rat (fst outerErrorTarget)
      |errorG|<target =
        estimateG
          increment 0#increment
          f[z]+increment∈Q
          |increment|<radiusG

      outerTerm : ℂ
      outerTerm =
        quotientF ·ℂ errorG

      innerTerm : ℂ
      innerTerm =
        derivativeG ·ℂ errorF

      |outerTerm|<half :
        modulus outerTerm <ᵣ rat (fst halfε)
      |outerTerm|<half =
        boundedComplexProductModulus<
          quotientF errorG quotientBoundF halfε
          |quotientF|≤bound |errorG|<target

      |innerTerm|<half :
        modulus innerTerm <ᵣ rat (fst halfε)
      |innerTerm|<half =
        boundedComplexProductModulus<
          derivativeG errorF derivativeBoundG halfε
          |derivativeG|≤derivativeBoundG
          |errorF|<target

      compositionErrorBound :
        modulus (outerTerm +ℂ innerTerm)
          <ᵣ rat (fst ε)
      compositionErrorBound =
        modulusSumOfHalves<
          ε outerTerm innerTerm
          |outerTerm|<half |innerTerm|<half
    in
    subst (_<ᵣ rat (fst ε))
      (sym
        (cong modulus
          (composeDerivativeError
            g derivativeG f derivativeF z h
            0#h 0#increment)))
      compositionErrorBound


complexDifferentiableWithinAt-compose :
  ∀ {P Q g f z}
  (mapsInto : MapsComplexPredicates f P Q)
  (preservesApart :
    LocallyPreservesApartIncrementsWithinAt P f z)
  (differentiableF :
    ComplexDifferentiableWithinAt P f z)
  (differentiableG :
    ComplexDifferentiableWithinAt Q g (f z)) →
  ComplexScalarBound (fst differentiableF) →
  ComplexScalarBound (fst differentiableG) →
  ComplexDifferentiableWithinAt P
    (composeComplexFunctions g f) z
complexDifferentiableWithinAt-compose
  {P} {Q} {g} {f} {z}
  mapsInto preservesApart
  differentiableF differentiableG
  derivativeBoundF derivativeBoundG =
  fst differentiableG ·ℂ fst differentiableF ,
  hasComplexDerivativeWithinAt-compose
    {P = P} {Q = Q}
    {g = g} {derivativeG = fst differentiableG}
    {f = f} {derivativeF = fst differentiableF}
    {z = z}
    mapsInto preservesApart
    derivativeBoundF derivativeBoundG
    (snd differentiableF) (snd differentiableG)


holomorphicOn-compose :
  ∀ {P Q g f}
  (mapsInto : MapsComplexPredicates f P Q)
  (preservesApart :
    (z : ℂ) → z ∈ P →
    LocallyPreservesApartIncrementsWithinAt P f z)
  (holomorphicF : HolomorphicOn P f)
  (holomorphicG : HolomorphicOn Q g) →
  ((z : ℂ) → (z∈P : z ∈ P) →
    ComplexScalarBound (fst (holomorphicF z z∈P))) →
  ((z : ℂ) → (z∈P : z ∈ P) →
    ComplexScalarBound
      (fst (holomorphicG
        (f z) (mapsInto z z∈P)))) →
  HolomorphicOn P (composeComplexFunctions g f)
holomorphicOn-compose
  {P} {Q} {g} {f}
  mapsInto preservesApart
  holomorphicF holomorphicG
  derivativeBoundF derivativeBoundG z z∈P =
  complexDifferentiableWithinAt-compose
    {P = P} {Q = Q} {g = g} {f = f} {z = z}
    mapsInto (preservesApart z z∈P)
    (holomorphicF z z∈P)
    (holomorphicG (f z) (mapsInto z z∈P))
    (derivativeBoundF z z∈P)
    (derivativeBoundG z z∈P)


identityMapsComplexPredicate :
  ∀ P → MapsComplexPredicates (λ z → z) P P
identityMapsComplexPredicate P z z∈P = z∈P


identityInnerIncrementPath : ∀ z h →
  innerIncrement (λ w → w) z h ≡ h
identityInnerIncrementPath z h =
  ℂ≡ ℝ! ℝ!


identityPreservesApartIncrementsWithinAt :
  ∀ P z →
  PreservesApartIncrementsWithinAt P (λ w → w) z
identityPreservesApartIncrementsWithinAt
  P z h 0#h _ =
  subst (0ℂ #ℂ_)
    (sym (identityInnerIncrementPath z h))
    0#h


identityPreservesApartIncrementsAt :
  ∀ z →
  PreservesApartIncrementsAt (λ w → w) z
identityPreservesApartIncrementsAt z h 0#h =
  subst (0ℂ #ℂ_)
    (sym (identityInnerIncrementPath z h))
    0#h


identityLocallyPreservesApartIncrementsAt :
  ∀ z →
  LocallyPreservesApartIncrementsAt (λ w → w) z
identityLocallyPreservesApartIncrementsAt z =
  preservesApartIncrementsAt→Locally
    {f = λ w → w} {z = z}
    (identityPreservesApartIncrementsAt z)


affineInnerIncrementPath : ∀ a b z h →
  innerIncrement (affineℂ a b) z h ≡ a ·ℂ h
affineInnerIncrementPath a b z h =
  ℂ≡ ℝ! ℝ!


affinePreservesApartIncrementsWithinAt :
  ∀ P a b z →
  0ℂ #ℂ a →
  PreservesApartIncrementsWithinAt P (affineℂ a b) z
affinePreservesApartIncrementsWithinAt
  P a b z 0#a h 0#h _ =
  subst (0ℂ #ℂ_)
    (sym (affineInnerIncrementPath a b z h))
    (0#ℂ-mul 0#a 0#h)


affinePreservesApartIncrementsAt :
  ∀ a b z →
  0ℂ #ℂ a →
  PreservesApartIncrementsAt (affineℂ a b) z
affinePreservesApartIncrementsAt
  a b z 0#a h 0#h =
  subst (0ℂ #ℂ_)
    (sym (affineInnerIncrementPath a b z h))
    (0#ℂ-mul 0#a 0#h)


affineLocallyPreservesApartIncrementsAt :
  ∀ a b z →
  0ℂ #ℂ a →
  LocallyPreservesApartIncrementsAt (affineℂ a b) z
affineLocallyPreservesApartIncrementsAt
  a b z 0#a =
  preservesApartIncrementsAt→Locally
    {f = affineℂ a b} {z = z}
    (affinePreservesApartIncrementsAt
      a b z 0#a)
