module Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Product where

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
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Inverse.Definition
open import Cubical.HITs.CauchyReals.Complex.Inverse.Cancellation
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.Bounds
open import Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality
open import Cubical.HITs.CauchyReals.Complex.Domain
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Within
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra.Addition

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


multiplyComplexFunctions : (ℂ → ℂ) → (ℂ → ℂ) → ℂ → ℂ
multiplyComplexFunctions f g z = f z ·ℂ g z


productDifferencePath : ∀ x x₀ y y₀ →
  x ·ℂ y -ℂ x₀ ·ℂ y₀ ≡
  (x -ℂ x₀) ·ℂ y₀ +ℂ x ·ℂ (y -ℂ y₀)
productDifferencePath x x₀ y y₀ =
  ℂ≡ ℝ! ℝ!


productDifferenceNumerator :
  ∀ f g z h →
  multiplyComplexFunctions f g (z +ℂ h)
    -ℂ multiplyComplexFunctions f g z ≡
  (f (z +ℂ h) -ℂ f z) ·ℂ g z
    +ℂ
  f (z +ℂ h) ·ℂ (g (z +ℂ h) -ℂ g z)
productDifferenceNumerator f g z h =
  productDifferencePath
    (f (z +ℂ h)) (f z)
    (g (z +ℂ h)) (g z)


productDividePath : ∀ x y a b u →
  ((x ·ℂ a) +ℂ (b ·ℂ y)) ·ℂ u ≡
  ((x ·ℂ u) ·ℂ a) +ℂ (b ·ℂ (y ·ℂ u))
productDividePath x y a b u =
  ℂ≡ ℝ! ℝ!


productDifferenceQuotient :
  ∀ f g z h (0#h : 0ℂ #ℂ h) →
  DifferenceQuotient (multiplyComplexFunctions f g) z h 0#h ≡
  DifferenceQuotient f z h 0#h ·ℂ g z
    +ℂ
  f (z +ℂ h) ·ℂ DifferenceQuotient g z h 0#h
productDifferenceQuotient f g z h 0#h =
  cong (_／ℂ[ h , 0#h ])
    (productDifferenceNumerator f g z h)
  ∙ productDividePath
      (f (z +ℂ h) -ℂ f z)
      (g (z +ℂ h) -ℂ g z)
      (g z) (f (z +ℂ h))
      (invℂ h 0#h)


divideReconstruct :
  ∀ x h (0#h : 0ℂ #ℂ h) →
  x ≡ h ·ℂ (x ／ℂ[ h , 0#h ])
divideReconstruct x h 0#h =
  sym
    (·ℂComm h (x ／ℂ[ h , 0#h ])
    ∙ [x/y]·yℂ x h 0#h)


differenceReconstructPath : ∀ x y →
  x ≡ y +ℂ (x -ℂ y)
differenceReconstructPath x y =
  ℂ≡ ℝ! ℝ!


differenceQuotientReconstruct :
  ∀ f z h (0#h : 0ℂ #ℂ h) →
  f (z +ℂ h) ≡
  f z +ℂ h ·ℂ DifferenceQuotient f z h 0#h
differenceQuotientReconstruct f z h 0#h =
  differenceReconstructPath (f (z +ℂ h)) (f z)
  ∙ cong (f z +ℂ_)
      (divideReconstruct
        (f (z +ℂ h) -ℂ f z) h 0#h)


productDifferenceQuotientExpanded :
  ∀ f g z h (0#h : 0ℂ #ℂ h) →
  DifferenceQuotient (multiplyComplexFunctions f g) z h 0#h ≡
  DifferenceQuotient f z h 0#h ·ℂ g z
    +ℂ
  (f z +ℂ h ·ℂ DifferenceQuotient f z h 0#h)
    ·ℂ DifferenceQuotient g z h 0#h
productDifferenceQuotientExpanded f g z h 0#h =
  productDifferenceQuotient f g z h 0#h
  ∙ cong
      (λ valueAtH →
        DifferenceQuotient f z h 0#h ·ℂ g z
          +ℂ valueAtH ·ℂ DifferenceQuotient g z h 0#h)
      (differenceQuotientReconstruct f z h 0#h)


productDerivativeErrorPath :
  ∀ quotientF quotientG derivativeF derivativeG valueF valueG h →
  (quotientF ·ℂ valueG
    +ℂ (valueF +ℂ h ·ℂ quotientF) ·ℂ quotientG)
    -ℂ
  (derivativeF ·ℂ valueG +ℂ valueF ·ℂ derivativeG)
  ≡
  valueG ·ℂ (quotientF -ℂ derivativeF)
    +ℂ
  valueF ·ℂ (quotientG -ℂ derivativeG)
    +ℂ
  (quotientF ·ℂ quotientG) ·ℂ h
productDerivativeErrorPath
  quotientF quotientG derivativeF derivativeG valueF valueG h =
  ℂ≡ ℝ! ℝ!


productDerivativeError :
  ∀ f derivativeF g derivativeG z h (0#h : 0ℂ #ℂ h) →
  DifferenceQuotient (multiplyComplexFunctions f g) z h 0#h
    -ℂ
  (derivativeF ·ℂ g z +ℂ f z ·ℂ derivativeG)
  ≡
  g z ·ℂ
    (DifferenceQuotient f z h 0#h -ℂ derivativeF)
    +ℂ
  f z ·ℂ
    (DifferenceQuotient g z h 0#h -ℂ derivativeG)
    +ℂ
  (DifferenceQuotient f z h 0#h
    ·ℂ DifferenceQuotient g z h 0#h)
    ·ℂ h
productDerivativeError
  f derivativeF g derivativeG z h 0#h =
  cong
    (_-ℂ (derivativeF ·ℂ g z +ℂ f z ·ℂ derivativeG))
    (productDifferenceQuotientExpanded f g z h 0#h)
  ∙ productDerivativeErrorPath
      (DifferenceQuotient f z h 0#h)
      (DifferenceQuotient g z h 0#h)
      derivativeF derivativeG (f z) (g z) h


quotientAsErrorPlusDerivative : ∀ quotient derivative →
  quotient ≡ (quotient -ℂ derivative) +ℂ derivative
quotientAsErrorPlusDerivative quotient derivative =
  ℂ≡ ℝ! ℝ!


oneℚ₊ : ℚ₊
oneℚ₊ = 1


quotientModulusBound :
  ∀ quotient derivative (M : ℚ₊) →
  modulus derivative ≤ᵣ rat (fst M) →
  modulus (quotient -ℂ derivative) <ᵣ rat (fst oneℚ₊) →
  modulus quotient ≤ᵣ rat (fst (oneℚ₊ +₊ M))
quotientModulusBound
  quotient derivative M |derivative|≤M |error|<1 =
  isTrans≡≤ᵣ _ _ _
    (cong modulus
      (quotientAsErrorPlusDerivative quotient derivative))
    (isTrans≤≡ᵣ _ _ _
      (isTrans≤ᵣ _ _ _
        (modulus-triangle
          (quotient -ℂ derivative) derivative)
        (≤ᵣMonotone+ᵣ _ _ _ _
          (<ᵣWeaken≤ᵣ _ _ |error|<1)
          |derivative|≤M))
      (+ᵣ-rat
        (fst oneℚ₊) (fst M)))


quotientProductModulusBound :
  ∀ quotientF quotientG (boundF boundG : ℚ₊) →
  modulus quotientF ≤ᵣ rat (fst boundF) →
  modulus quotientG ≤ᵣ rat (fst boundG) →
  modulus (quotientF ·ℂ quotientG)
    ≤ᵣ rat (fst (boundF ·₊ boundG))
quotientProductModulusBound
  quotientF quotientG boundF boundG
  |quotientF|≤boundF |quotientG|≤boundG =
  isTrans≡≤ᵣ _ _ _
    (modulus-mul quotientF quotientG)
    (isTrans≤≡ᵣ _ _ _
      (≤ᵣ₊Monotone·ᵣ
        (modulus quotientF) (rat (fst boundF))
        (modulus quotientG) (rat (fst boundG))
        (<ᵣWeaken≤ᵣ _ _
          (snd (ℚ₊→ℝ₊ boundF)))
        (modulusNonNeg quotientG)
        |quotientF|≤boundF |quotientG|≤boundG)
      (sym (rat·ᵣrat (fst boundF) (fst boundG))))


boundedComplexProductModulus< :
  ∀ c error (M ε : ℚ₊) →
  modulus c ≤ᵣ rat (fst M) →
  modulus error
    <ᵣ rat (fst ((ℚ._⁻¹₊ M) ·₊ ε)) →
  modulus (c ·ℂ error) <ᵣ rat (fst ε)
boundedComplexProductModulus<
  c error M ε |c|≤M |error|<η =
  isTrans≡<ᵣ _ _ _
    (modulus-mul c error)
    (boundedModulusProduct<
      c error M ε |c|≤M |error|<η)


modulus<nestedMin→first :
  ∀ h δ η θ →
  modulus h <ᵣ rat (fst (min₊ (min₊ δ η) θ)) →
  modulus h <ᵣ rat (fst δ)
modulus<nestedMin→first h δ η θ |h|<min =
  modulus<min→left h δ η
    (modulus<min→left h (min₊ δ η) θ |h|<min)


modulus<nestedMin→second :
  ∀ h δ η θ →
  modulus h <ᵣ rat (fst (min₊ (min₊ δ η) θ)) →
  modulus h <ᵣ rat (fst η)
modulus<nestedMin→second h δ η θ |h|<min =
  modulus<min→right h δ η
    (modulus<min→left h (min₊ δ η) θ |h|<min)


modulus<nestedMin→third :
  ∀ h δ η θ →
  modulus h <ᵣ rat (fst (min₊ (min₊ δ η) θ)) →
  modulus h <ᵣ rat (fst θ)
modulus<nestedMin→third h δ η θ |h|<min =
  modulus<min→right h (min₊ δ η) θ |h|<min


modulusTripleProductSum< :
  ∀ ε termF termG cross →
  modulus termF
    <ᵣ rat (fst ((ε /2₊) /2₊)) →
  modulus termG
    <ᵣ rat (fst ((ε /2₊) /2₊)) →
  modulus cross <ᵣ rat (fst (ε /2₊)) →
  modulus ((termF +ℂ termG) +ℂ cross)
    <ᵣ rat (fst ε)
modulusTripleProductSum<
  ε termF termG cross |termF|<ε/4 |termG|<ε/4 |cross|<ε/2 =
  modulusSumOfHalves<
    ε (termF +ℂ termG) cross
    (modulusSumOfHalves<
      (ε /2₊) termF termG
      |termF|<ε/4 |termG|<ε/4)
    |cross|<ε/2


hasComplexDerivativeWithinAt-mul :
  ∀ {P f derivativeF g derivativeG z} →
  ComplexScalarBound (f z) →
  ComplexScalarBound derivativeF →
  ComplexScalarBound (g z) →
  ComplexScalarBound derivativeG →
  HasComplexDerivativeWithinAt P f derivativeF z →
  HasComplexDerivativeWithinAt P g derivativeG z →
  HasComplexDerivativeWithinAt P
    (multiplyComplexFunctions f g)
    (derivativeF ·ℂ g z +ℂ f z ·ℂ derivativeG) z
hasComplexDerivativeWithinAt-mul
  {P} {f} {derivativeF} {g} {derivativeG} {z}
  (valueBoundF , |f[z]|≤valueBoundF)
  (derivativeBoundF , |derivativeF|≤derivativeBoundF)
  (valueBoundG , |g[z]|≤valueBoundG)
  (derivativeBoundG , |derivativeG|≤derivativeBoundG)
  derivativeFAt derivativeGAt ε =
  let
    quarterε : ℚ₊
    quarterε = (ε /2₊) /2₊

    errorTargetF : ℚ₊
    errorTargetF =
      (ℚ._⁻¹₊ valueBoundG) ·₊ quarterε

    errorTargetG : ℚ₊
    errorTargetG =
      (ℚ._⁻¹₊ valueBoundF) ·₊ quarterε

    derivativeToleranceF : ℚ₊
    derivativeToleranceF =
      min₊ errorTargetF oneℚ₊

    derivativeToleranceG : ℚ₊
    derivativeToleranceG =
      min₊ errorTargetG oneℚ₊

    radiusF , estimateF =
      derivativeFAt derivativeToleranceF

    radiusG , estimateG =
      derivativeGAt derivativeToleranceG

    quotientBoundF : ℚ₊
    quotientBoundF =
      oneℚ₊ +₊ derivativeBoundF

    quotientBoundG : ℚ₊
    quotientBoundG =
      oneℚ₊ +₊ derivativeBoundG

    quotientProductBound : ℚ₊
    quotientProductBound =
      quotientBoundF ·₊ quotientBoundG

    crossRadius : ℚ₊
    crossRadius =
      (ℚ._⁻¹₊ quotientProductBound) ·₊ (ε /2₊)

    radius : ℚ₊
    radius =
      min₊ (min₊ radiusF radiusG) crossRadius
  in
  radius ,
  λ h 0#h z+h∈P |h|<radius →
    let
      quotientF : ℂ
      quotientF =
        DifferenceQuotient f z h 0#h

      quotientG : ℂ
      quotientG =
        DifferenceQuotient g z h 0#h

      errorF : ℂ
      errorF = quotientF -ℂ derivativeF

      errorG : ℂ
      errorG = quotientG -ℂ derivativeG

      |h|<radiusF :
        modulus h <ᵣ rat (fst radiusF)
      |h|<radiusF =
        modulus<nestedMin→first
          h radiusF radiusG crossRadius |h|<radius

      |h|<radiusG :
        modulus h <ᵣ rat (fst radiusG)
      |h|<radiusG =
        modulus<nestedMin→second
          h radiusF radiusG crossRadius |h|<radius

      |h|<crossRadius :
        modulus h <ᵣ rat (fst crossRadius)
      |h|<crossRadius =
        modulus<nestedMin→third
          h radiusF radiusG crossRadius |h|<radius

      |errorF|<tolerance :
        modulus errorF
          <ᵣ rat (fst derivativeToleranceF)
      |errorF|<tolerance =
        estimateF h 0#h z+h∈P |h|<radiusF

      |errorG|<tolerance :
        modulus errorG
          <ᵣ rat (fst derivativeToleranceG)
      |errorG|<tolerance =
        estimateG h 0#h z+h∈P |h|<radiusG

      |errorF|<target :
        modulus errorF <ᵣ rat (fst errorTargetF)
      |errorF|<target =
        modulus<min→left
          errorF errorTargetF oneℚ₊
          |errorF|<tolerance

      |errorG|<target :
        modulus errorG <ᵣ rat (fst errorTargetG)
      |errorG|<target =
        modulus<min→left
          errorG errorTargetG oneℚ₊
          |errorG|<tolerance

      |errorF|<1 :
        modulus errorF <ᵣ rat (fst oneℚ₊)
      |errorF|<1 =
        modulus<min→right
          errorF errorTargetF oneℚ₊
          |errorF|<tolerance

      |errorG|<1 :
        modulus errorG <ᵣ rat (fst oneℚ₊)
      |errorG|<1 =
        modulus<min→right
          errorG errorTargetG oneℚ₊
          |errorG|<tolerance

      |quotientF|≤bound :
        modulus quotientF
          ≤ᵣ rat (fst quotientBoundF)
      |quotientF|≤bound =
        quotientModulusBound
          quotientF derivativeF derivativeBoundF
          |derivativeF|≤derivativeBoundF
          |errorF|<1

      |quotientG|≤bound :
        modulus quotientG
          ≤ᵣ rat (fst quotientBoundG)
      |quotientG|≤bound =
        quotientModulusBound
          quotientG derivativeG derivativeBoundG
          |derivativeG|≤derivativeBoundG
          |errorG|<1

      |quotientF·quotientG|≤bound :
        modulus (quotientF ·ℂ quotientG)
          ≤ᵣ rat (fst quotientProductBound)
      |quotientF·quotientG|≤bound =
        quotientProductModulusBound
          quotientF quotientG
          quotientBoundF quotientBoundG
          |quotientF|≤bound |quotientG|≤bound

      termF : ℂ
      termF = g z ·ℂ errorF

      termG : ℂ
      termG = f z ·ℂ errorG

      cross : ℂ
      cross = (quotientF ·ℂ quotientG) ·ℂ h

      |termF|<quarter :
        modulus termF <ᵣ rat (fst quarterε)
      |termF|<quarter =
        boundedComplexProductModulus<
          (g z) errorF valueBoundG quarterε
          |g[z]|≤valueBoundG |errorF|<target

      |termG|<quarter :
        modulus termG <ᵣ rat (fst quarterε)
      |termG|<quarter =
        boundedComplexProductModulus<
          (f z) errorG valueBoundF quarterε
          |f[z]|≤valueBoundF |errorG|<target

      |cross|<half :
        modulus cross <ᵣ rat (fst (ε /2₊))
      |cross|<half =
        boundedComplexProductModulus<
          (quotientF ·ℂ quotientG) h
          quotientProductBound (ε /2₊)
          |quotientF·quotientG|≤bound
          |h|<crossRadius

      productErrorBound :
        modulus ((termF +ℂ termG) +ℂ cross)
          <ᵣ rat (fst ε)
      productErrorBound =
        modulusTripleProductSum<
          ε termF termG cross
          |termF|<quarter |termG|<quarter |cross|<half
    in
    subst (_<ᵣ rat (fst ε))
      (sym
        (cong modulus
          (productDerivativeError
            f derivativeF g derivativeG z h 0#h)))
      productErrorBound


complexDifferentiableWithinAt-mul :
  ∀ {P f g z}
  (differentiableF :
    ComplexDifferentiableWithinAt P f z)
  (differentiableG :
    ComplexDifferentiableWithinAt P g z) →
  ComplexScalarBound (f z) →
  ComplexScalarBound (fst differentiableF) →
  ComplexScalarBound (g z) →
  ComplexScalarBound (fst differentiableG) →
  ComplexDifferentiableWithinAt P
    (multiplyComplexFunctions f g) z
complexDifferentiableWithinAt-mul
  {P} {f} {g} {z}
  differentiableF differentiableG
  valueBoundF derivativeBoundF
  valueBoundG derivativeBoundG =
  (fst differentiableF ·ℂ g z
    +ℂ f z ·ℂ fst differentiableG) ,
  hasComplexDerivativeWithinAt-mul
    {P = P} {f = f}
    {derivativeF = fst differentiableF}
    {g = g}
    {derivativeG = fst differentiableG}
    {z = z}
    valueBoundF derivativeBoundF
    valueBoundG derivativeBoundG
    (snd differentiableF) (snd differentiableG)


holomorphicOn-mul :
  ∀ {P f g}
  (holomorphicF : HolomorphicOn P f)
  (holomorphicG : HolomorphicOn P g) →
  ((z : ℂ) → z ∈ P → ComplexScalarBound (f z)) →
  ((z : ℂ) → (z∈P : z ∈ P) →
    ComplexScalarBound (fst (holomorphicF z z∈P))) →
  ((z : ℂ) → z ∈ P → ComplexScalarBound (g z)) →
  ((z : ℂ) → (z∈P : z ∈ P) →
    ComplexScalarBound (fst (holomorphicG z z∈P))) →
  HolomorphicOn P (multiplyComplexFunctions f g)
holomorphicOn-mul
  {P} {f} {g} holomorphicF holomorphicG
  valueBoundF derivativeBoundF
  valueBoundG derivativeBoundG z z∈P =
  complexDifferentiableWithinAt-mul
    {P = P} {f = f} {g = g} {z = z}
    (holomorphicF z z∈P) (holomorphicG z z∈P)
    (valueBoundF z z∈P)
    (derivativeBoundF z z∈P)
    (valueBoundG z z∈P)
    (derivativeBoundG z z∈P)
