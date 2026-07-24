module Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Inverse where

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


ReciprocalOn :
  ComplexPredicate → (ℂ → ℂ) → (ℂ → ℂ) → Type₀
ReciprocalOn P f g =
  (w : ℂ) → w ∈ P → f w ·ℂ g w ≡ 1ℂ


WitnessedInverseExtensionOn :
  ComplexPredicate → (ℂ → ℂ) → (ℂ → ℂ) → Type₀
WitnessedInverseExtensionOn P f g =
  (w : ℂ) → w ∈ P →
  Σ[ 0#fw ∈ 0ℂ #ℂ f w ]
    g w ≡ invℂ (f w) 0#fw


witnessedInverseExtensionOn→ReciprocalOn :
  ∀ {P f g} →
  WitnessedInverseExtensionOn P f g →
  ReciprocalOn P f g
witnessedInverseExtensionOn→ReciprocalOn
  {P} {f} {g} inverseExtension w w∈P =
  let
    0#fw , inversePath =
      inverseExtension w w∈P
  in
  cong (f w ·ℂ_) inversePath
  ∙ ·invℂ (f w) 0#fw


ComplexLocalBoundWithinAt :
  ComplexPredicate → (ℂ → ℂ) → ℂ → Type₀
ComplexLocalBoundWithinAt P g z =
  Σ[ radius ∈ ℚ₊ ]
  Σ[ bound ∈ ℚ₊ ]
    ((h : ℂ) → z +ℂ h ∈ P →
      modulus h <ᵣ rat (fst radius) →
      modulus (g (z +ℂ h))
        ≤ᵣ rat (fst bound))


reciprocalDerivative :
  (ℂ → ℂ) → ℂ → ℂ → ℂ
reciprocalDerivative g derivativeF z =
  ((-ℂ g z) ·ℂ derivativeF) ·ℂ g z


reciprocalDifferenceExpansion :
  ∀ f₁ g₁ f₀ g₀ →
  ((-ℂ g₁) ·ℂ (f₁ -ℂ f₀)) ·ℂ g₀ ≡
  (-ℂ (f₁ ·ℂ g₁)) ·ℂ g₀
    +ℂ g₁ ·ℂ (f₀ ·ℂ g₀)
reciprocalDifferenceExpansion f₁ g₁ f₀ g₀ =
  ℂ≡ ℝ! ℝ!


reciprocalDifferenceCollapse :
  ∀ f₁ g₁ f₀ g₀ →
  f₁ ·ℂ g₁ ≡ 1ℂ →
  f₀ ·ℂ g₀ ≡ 1ℂ →
  (-ℂ (f₁ ·ℂ g₁)) ·ℂ g₀
    +ℂ g₁ ·ℂ (f₀ ·ℂ g₀)
  ≡
  g₁ -ℂ g₀
reciprocalDifferenceCollapse
  f₁ g₁ f₀ g₀ product₁ product₀ =
  cong₂ _+ℂ_
    (cong (λ value → (-ℂ value) ·ℂ g₀)
      product₁)
    (cong (g₁ ·ℂ_) product₀)
  ∙ ℂ≡ ℝ! ℝ!


reciprocalDifference :
  ∀ f₁ g₁ f₀ g₀ →
  f₁ ·ℂ g₁ ≡ 1ℂ →
  f₀ ·ℂ g₀ ≡ 1ℂ →
  g₁ -ℂ g₀ ≡
  ((-ℂ g₁) ·ℂ (f₁ -ℂ f₀)) ·ℂ g₀
reciprocalDifference
  f₁ g₁ f₀ g₀ product₁ product₀ =
  sym
    (reciprocalDifferenceExpansion
      f₁ g₁ f₀ g₀
    ∙ reciprocalDifferenceCollapse
        f₁ g₁ f₀ g₀ product₁ product₀)


reciprocalDivideReorder :
  ∀ g₁ difference g₀ inverseH →
  (((-ℂ g₁) ·ℂ difference) ·ℂ g₀)
    ·ℂ inverseH
  ≡
  ((-ℂ g₁) ·ℂ (difference ·ℂ inverseH))
    ·ℂ g₀
reciprocalDivideReorder g₁ difference g₀ inverseH =
  ℂ≡ ℝ! ℝ!


reciprocalDifferenceQuotient :
  ∀ {P} f g z h (0#h : 0ℂ #ℂ h) →
  z ∈ P →
  z +ℂ h ∈ P →
  ReciprocalOn P f g →
  DifferenceQuotient g z h 0#h ≡
  ((-ℂ g (z +ℂ h))
    ·ℂ DifferenceQuotient f z h 0#h)
    ·ℂ g z
reciprocalDifferenceQuotient
  {P} f g z h 0#h z∈P z+h∈P reciprocal =
  cong (_／ℂ[ h , 0#h ])
    (reciprocalDifference
      (f (z +ℂ h)) (g (z +ℂ h))
      (f z) (g z)
      (reciprocal (z +ℂ h) z+h∈P)
      (reciprocal z z∈P))
  ∙ reciprocalDivideReorder
      (g (z +ℂ h))
      (f (z +ℂ h) -ℂ f z)
      (g z)
      (invℂ h 0#h)


reciprocalDifferenceAsQuotientProduct :
  ∀ {P} f g z h (0#h : 0ℂ #ℂ h) →
  z ∈ P →
  z +ℂ h ∈ P →
  ReciprocalOn P f g →
  g (z +ℂ h) -ℂ g z ≡
  ((-ℂ g (z +ℂ h))
    ·ℂ
   (h ·ℂ DifferenceQuotient f z h 0#h))
    ·ℂ g z
reciprocalDifferenceAsQuotientProduct
  {P} f g z h 0#h z∈P z+h∈P reciprocal =
  reciprocalDifference
    (f (z +ℂ h)) (g (z +ℂ h))
    (f z) (g z)
    (reciprocal (z +ℂ h) z+h∈P)
    (reciprocal z z∈P)
  ∙ cong
      (λ difference →
        ((-ℂ g (z +ℂ h)) ·ℂ difference)
          ·ℂ g z)
      (divideReconstruct
        (f (z +ℂ h) -ℂ f z) h 0#h)


reciprocalDerivativeErrorSplit :
  ∀ nearbyG valueG quotientF derivativeF →
  (((-ℂ nearbyG) ·ℂ quotientF) ·ℂ valueG)
    -ℂ reciprocalDerivative
      (λ _ → valueG) derivativeF valueG
  ≡
  (-ℂ valueG)
    ·ℂ
  (valueG
    ·ℂ (quotientF -ℂ derivativeF))
  +ℂ
  (((-ℂ (nearbyG -ℂ valueG))
    ·ℂ quotientF)
    ·ℂ valueG)
reciprocalDerivativeErrorSplit
  nearbyG valueG quotientF derivativeF =
  ℂ≡ ℝ! ℝ!


reciprocalCrossSubstitute :
  ∀ nearbyG valueG quotientF h →
  nearbyG -ℂ valueG ≡
    (((-ℂ nearbyG)
      ·ℂ (h ·ℂ quotientF))
      ·ℂ valueG) →
  (((-ℂ (nearbyG -ℂ valueG))
    ·ℂ quotientF)
    ·ℂ valueG)
  ≡
  nearbyG
    ·ℂ
  (quotientF
    ·ℂ
  (quotientF
    ·ℂ
  (valueG
    ·ℂ (valueG ·ℂ h))))
reciprocalCrossSubstitute
  nearbyG valueG quotientF h inverseDifference =
  cong
    (λ difference →
      ((-ℂ difference) ·ℂ quotientF)
        ·ℂ valueG)
    inverseDifference
  ∙ ℂ≡ ℝ! ℝ!


reciprocalDerivativeError :
  ∀ {P} f derivativeF g z h
  (0#h : 0ℂ #ℂ h) →
  z ∈ P →
  z +ℂ h ∈ P →
  ReciprocalOn P f g →
  DifferenceQuotient g z h 0#h
    -ℂ reciprocalDerivative g derivativeF z
  ≡
  (-ℂ g z)
    ·ℂ
  (g z
    ·ℂ
  (DifferenceQuotient f z h 0#h
    -ℂ derivativeF))
  +ℂ
  g (z +ℂ h)
    ·ℂ
  (DifferenceQuotient f z h 0#h
    ·ℂ
  (DifferenceQuotient f z h 0#h
    ·ℂ
  (g z
    ·ℂ (g z ·ℂ h))))
reciprocalDerivativeError
  {P} f derivativeF g z h 0#h
  z∈P z+h∈P reciprocal =
  cong
    (_-ℂ reciprocalDerivative g derivativeF z)
    (reciprocalDifferenceQuotient
      {P = P}
      f g z h 0#h z∈P z+h∈P reciprocal)
  ∙ reciprocalDerivativeErrorSplit
      (g (z +ℂ h)) (g z)
      (DifferenceQuotient f z h 0#h)
      derivativeF
  ∙ cong
      ((-ℂ g z)
        ·ℂ
       (g z
        ·ℂ
       (DifferenceQuotient f z h 0#h
        -ℂ derivativeF))
        +ℂ_)
      (reciprocalCrossSubstitute
        (g (z +ℂ h)) (g z)
        (DifferenceQuotient f z h 0#h)
        h
        (reciprocalDifferenceAsQuotientProduct
          {P = P}
          f g z h 0#h z∈P z+h∈P reciprocal))


negativeValueModulusBound :
  ∀ value (bound : ℚ₊) →
  modulus value ≤ᵣ rat (fst bound) →
  modulus (-ℂ value) ≤ᵣ rat (fst bound)
negativeValueModulusBound
  value bound |value|≤bound =
  isTrans≡≤ᵣ _ _ _
    (modulus-neg value)
    |value|≤bound


reciprocalLinearInnerModulus< :
  ∀ valueG errorF (bound ε : ℚ₊) →
  modulus valueG ≤ᵣ rat (fst bound) →
  modulus errorF
    <ᵣ
  rat
    (fst
      ((ℚ._⁻¹₊ bound)
        ·₊ ((ℚ._⁻¹₊ bound) ·₊ ε))) →
  modulus (valueG ·ℂ errorF)
    <ᵣ
  rat (fst ((ℚ._⁻¹₊ bound) ·₊ ε))
reciprocalLinearInnerModulus<
  valueG errorF bound ε
  |valueG|≤bound |errorF|<target =
  boundedComplexProductModulus<
    valueG errorF bound
    ((ℚ._⁻¹₊ bound) ·₊ ε)
    |valueG|≤bound |errorF|<target


reciprocalLinearOuterModulus< :
  ∀ valueG errorF (bound ε : ℚ₊) →
  modulus valueG ≤ᵣ rat (fst bound) →
  modulus (valueG ·ℂ errorF)
    <ᵣ
  rat (fst ((ℚ._⁻¹₊ bound) ·₊ ε)) →
  modulus
    ((-ℂ valueG) ·ℂ (valueG ·ℂ errorF))
    <ᵣ rat (fst ε)
reciprocalLinearOuterModulus<
  valueG errorF bound ε
  |valueG|≤bound |innerError|<target =
  boundedComplexProductModulus<
    (-ℂ valueG) (valueG ·ℂ errorF)
    bound ε
    (negativeValueModulusBound
      valueG bound |valueG|≤bound)
    |innerError|<target


opaque
  reciprocalLinearErrorModulus< :
    ∀ valueG errorF (bound ε : ℚ₊) →
    modulus valueG ≤ᵣ rat (fst bound) →
    modulus errorF
      <ᵣ
    rat
      (fst
        ((ℚ._⁻¹₊ bound)
          ·₊ ((ℚ._⁻¹₊ bound) ·₊ ε))) →
    modulus
      ((-ℂ valueG) ·ℂ (valueG ·ℂ errorF))
      <ᵣ rat (fst ε)
  reciprocalLinearErrorModulus<
    valueG errorF bound ε
    |valueG|≤bound |errorF|<target =
    reciprocalLinearOuterModulus<
      valueG errorF bound ε
      |valueG|≤bound
      (reciprocalLinearInnerModulus<
        valueG errorF bound ε
        |valueG|≤bound |errorF|<target)


opaque
  reciprocalCrossErrorModulus< :
    ∀ nearbyG quotientF valueG h
    (nearbyBound quotientBound valueBound ε : ℚ₊) →
    modulus nearbyG ≤ᵣ rat (fst nearbyBound) →
    modulus quotientF ≤ᵣ rat (fst quotientBound) →
    modulus valueG ≤ᵣ rat (fst valueBound) →
    modulus h
      <ᵣ
    rat
      (fst
        ((ℚ._⁻¹₊ valueBound)
          ·₊
        ((ℚ._⁻¹₊ valueBound)
          ·₊
        ((ℚ._⁻¹₊ quotientBound)
          ·₊
        ((ℚ._⁻¹₊ quotientBound)
          ·₊
        ((ℚ._⁻¹₊ nearbyBound) ·₊ ε)))))) →
    modulus
      (nearbyG
        ·ℂ (quotientF
          ·ℂ (quotientF
            ·ℂ (valueG
              ·ℂ (valueG ·ℂ h)))))
      <ᵣ rat (fst ε)
  reciprocalCrossErrorModulus<
    nearbyG quotientF valueG h
    nearbyBound quotientBound valueBound ε
    |nearbyG|≤bound |quotientF|≤bound
    |valueG|≤bound |h|<target =
    let
      afterNearbyTarget : ℚ₊
      afterNearbyTarget =
        (ℚ._⁻¹₊ nearbyBound) ·₊ ε

      afterFirstQuotientTarget : ℚ₊
      afterFirstQuotientTarget =
        (ℚ._⁻¹₊ quotientBound)
          ·₊ afterNearbyTarget

      afterSecondQuotientTarget : ℚ₊
      afterSecondQuotientTarget =
        (ℚ._⁻¹₊ quotientBound)
          ·₊ afterFirstQuotientTarget

      afterFirstValueTarget : ℚ₊
      afterFirstValueTarget =
        (ℚ._⁻¹₊ valueBound)
          ·₊ afterSecondQuotientTarget

      firstValueBound :
        modulus (valueG ·ℂ h)
          <ᵣ rat (fst afterFirstValueTarget)
      firstValueBound =
        boundedComplexProductModulus<
          valueG h valueBound afterFirstValueTarget
          |valueG|≤bound |h|<target

      secondValueBound :
        modulus (valueG ·ℂ (valueG ·ℂ h))
          <ᵣ rat (fst afterSecondQuotientTarget)
      secondValueBound =
        boundedComplexProductModulus<
          valueG (valueG ·ℂ h)
          valueBound afterSecondQuotientTarget
          |valueG|≤bound firstValueBound

      firstQuotientBound :
        modulus
          (quotientF
            ·ℂ (valueG ·ℂ (valueG ·ℂ h)))
          <ᵣ rat (fst afterFirstQuotientTarget)
      firstQuotientBound =
        boundedComplexProductModulus<
          quotientF
          (valueG ·ℂ (valueG ·ℂ h))
          quotientBound afterFirstQuotientTarget
          |quotientF|≤bound secondValueBound

      secondQuotientBound :
        modulus
          (quotientF
            ·ℂ
          (quotientF
            ·ℂ (valueG ·ℂ (valueG ·ℂ h))))
          <ᵣ rat (fst afterNearbyTarget)
      secondQuotientBound =
        boundedComplexProductModulus<
          quotientF
          (quotientF
            ·ℂ (valueG ·ℂ (valueG ·ℂ h)))
          quotientBound afterNearbyTarget
          |quotientF|≤bound firstQuotientBound
    in
    boundedComplexProductModulus<
      nearbyG
      (quotientF
        ·ℂ
      (quotientF
        ·ℂ (valueG ·ℂ (valueG ·ℂ h))))
      nearbyBound ε
      |nearbyG|≤bound secondQuotientBound


hasComplexDerivativeWithinAt-reciprocal :
  ∀ {P f derivativeF g z} →
  ReciprocalOn P f g →
  z ∈ P →
  ComplexScalarBound derivativeF →
  ComplexScalarBound (g z) →
  ComplexLocalBoundWithinAt P g z →
  HasComplexDerivativeWithinAt P f derivativeF z →
  HasComplexDerivativeWithinAt P g
    (reciprocalDerivative g derivativeF z) z
hasComplexDerivativeWithinAt-reciprocal
  {P} {f} {derivativeF} {g} {z}
  reciprocal z∈P
  (derivativeBound , |derivativeF|≤bound)
  (valueBound , |g[z]|≤bound)
  (localRadius , nearbyBound , nearbyEstimate)
  derivativeFAt ε =
  let
    halfε : ℚ₊
    halfε =
      ε /2₊

    linearInnerTarget : ℚ₊
    linearInnerTarget =
      (ℚ._⁻¹₊ valueBound) ·₊ halfε

    linearErrorTarget : ℚ₊
    linearErrorTarget =
      (ℚ._⁻¹₊ valueBound)
        ·₊ linearInnerTarget

    derivativeTolerance : ℚ₊
    derivativeTolerance =
      min₊ linearErrorTarget oneℚ₊

    derivativeRadius , derivativeEstimate =
      derivativeFAt derivativeTolerance

    quotientBound : ℚ₊
    quotientBound =
      oneℚ₊ +₊ derivativeBound

    afterNearbyTarget : ℚ₊
    afterNearbyTarget =
      (ℚ._⁻¹₊ nearbyBound) ·₊ halfε

    afterFirstQuotientTarget : ℚ₊
    afterFirstQuotientTarget =
      (ℚ._⁻¹₊ quotientBound)
        ·₊ afterNearbyTarget

    afterSecondQuotientTarget : ℚ₊
    afterSecondQuotientTarget =
      (ℚ._⁻¹₊ quotientBound)
        ·₊ afterFirstQuotientTarget

    afterFirstValueTarget : ℚ₊
    afterFirstValueTarget =
      (ℚ._⁻¹₊ valueBound)
        ·₊ afterSecondQuotientTarget

    crossRadius : ℚ₊
    crossRadius =
      (ℚ._⁻¹₊ valueBound)
        ·₊ afterFirstValueTarget

    radius : ℚ₊
    radius =
      min₊
        (min₊ derivativeRadius localRadius)
        crossRadius
  in
  radius ,
  λ h 0#h z+h∈P |h|<radius →
    let
      quotientF : ℂ
      quotientF =
        DifferenceQuotient f z h 0#h

      derivativeError : ℂ
      derivativeError =
        quotientF -ℂ derivativeF

      |h|<derivativeRadius :
        modulus h <ᵣ rat (fst derivativeRadius)
      |h|<derivativeRadius =
        modulus<nestedMin→first
          h derivativeRadius localRadius crossRadius
          |h|<radius

      |h|<localRadius :
        modulus h <ᵣ rat (fst localRadius)
      |h|<localRadius =
        modulus<nestedMin→second
          h derivativeRadius localRadius crossRadius
          |h|<radius

      |h|<crossRadius :
        modulus h <ᵣ rat (fst crossRadius)
      |h|<crossRadius =
        modulus<nestedMin→third
          h derivativeRadius localRadius crossRadius
          |h|<radius

      |derivativeError|<tolerance :
        modulus derivativeError
          <ᵣ rat (fst derivativeTolerance)
      |derivativeError|<tolerance =
        derivativeEstimate
          h 0#h z+h∈P |h|<derivativeRadius

      |derivativeError|<linearTarget :
        modulus derivativeError
          <ᵣ rat (fst linearErrorTarget)
      |derivativeError|<linearTarget =
        modulus<min→left
          derivativeError
          linearErrorTarget oneℚ₊
          |derivativeError|<tolerance

      |derivativeError|<one :
        modulus derivativeError
          <ᵣ rat (fst oneℚ₊)
      |derivativeError|<one =
        modulus<min→right
          derivativeError
          linearErrorTarget oneℚ₊
          |derivativeError|<tolerance

      |quotientF|≤bound :
        modulus quotientF
          ≤ᵣ rat (fst quotientBound)
      |quotientF|≤bound =
        quotientModulusBound
          quotientF derivativeF derivativeBound
          |derivativeF|≤bound
          |derivativeError|<one

      |nearbyG|≤bound :
        modulus (g (z +ℂ h))
          ≤ᵣ rat (fst nearbyBound)
      |nearbyG|≤bound =
        nearbyEstimate h z+h∈P |h|<localRadius

      linearErrorBound :
        modulus
          ((-ℂ g z)
            ·ℂ (g z ·ℂ derivativeError))
          <ᵣ rat (fst halfε)
      linearErrorBound =
        reciprocalLinearErrorModulus<
          (g z) derivativeError valueBound halfε
          |g[z]|≤bound
          |derivativeError|<linearTarget

      crossErrorBound :
        modulus
          (g (z +ℂ h)
            ·ℂ
          (quotientF
            ·ℂ
          (quotientF
            ·ℂ
          (g z
            ·ℂ (g z ·ℂ h)))))
          <ᵣ rat (fst halfε)
      crossErrorBound =
        reciprocalCrossErrorModulus<
          (g (z +ℂ h)) quotientF (g z) h
          nearbyBound quotientBound valueBound halfε
          |nearbyG|≤bound |quotientF|≤bound
          |g[z]|≤bound |h|<crossRadius

      reciprocalErrorBound :
        modulus
          (((-ℂ g z)
            ·ℂ (g z ·ℂ derivativeError))
          +ℂ
           (g (z +ℂ h)
            ·ℂ
          (quotientF
            ·ℂ
          (quotientF
            ·ℂ
          (g z
            ·ℂ (g z ·ℂ h))))))
          <ᵣ rat (fst ε)
      reciprocalErrorBound =
        modulusSumOfHalves<
          ε
          ((-ℂ g z)
            ·ℂ (g z ·ℂ derivativeError))
          (g (z +ℂ h)
            ·ℂ
          (quotientF
            ·ℂ
          (quotientF
            ·ℂ
          (g z
            ·ℂ (g z ·ℂ h)))))
          linearErrorBound crossErrorBound
    in
    subst (_<ᵣ rat (fst ε))
      (sym
        (cong modulus
          (reciprocalDerivativeError
            {P = P}
            f derivativeF g z h 0#h
            z∈P z+h∈P reciprocal)))
      reciprocalErrorBound


complexDifferentiableWithinAt-reciprocal :
  ∀ {P f g z}
  (differentiableF :
    ComplexDifferentiableWithinAt P f z) →
  ReciprocalOn P f g →
  z ∈ P →
  ComplexScalarBound (fst differentiableF) →
  ComplexScalarBound (g z) →
  ComplexLocalBoundWithinAt P g z →
  ComplexDifferentiableWithinAt P g z
complexDifferentiableWithinAt-reciprocal
  {P} {f} {g} {z}
  differentiableF reciprocal z∈P
  derivativeBound valueBound localBound =
  reciprocalDerivative g (fst differentiableF) z ,
  hasComplexDerivativeWithinAt-reciprocal
    {P = P}
    {f = f}
    {derivativeF = fst differentiableF}
    {g = g}
    {z = z}
    reciprocal z∈P
    derivativeBound valueBound localBound
    (snd differentiableF)


holomorphicOn-reciprocal :
  ∀ {P f g}
  (holomorphicF : HolomorphicOn P f) →
  ReciprocalOn P f g →
  ((z : ℂ) → (z∈P : z ∈ P) →
    ComplexScalarBound
      (fst (holomorphicF z z∈P))) →
  ((z : ℂ) → z ∈ P →
    ComplexScalarBound (g z)) →
  ((z : ℂ) → z ∈ P →
    ComplexLocalBoundWithinAt P g z) →
  HolomorphicOn P g
holomorphicOn-reciprocal
  {P} {f} {g}
  holomorphicF reciprocal
  derivativeBound valueBound localBound
  z z∈P =
  complexDifferentiableWithinAt-reciprocal
    {P = P} {f = f} {g = g} {z = z}
    (holomorphicF z z∈P)
    reciprocal z∈P
    (derivativeBound z z∈P)
    (valueBound z z∈P)
    (localBound z z∈P)
