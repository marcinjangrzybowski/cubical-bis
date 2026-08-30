module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.GeometricTail where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.List using (List ; length)
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Sum using (inl)

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Signed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (x≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Polynomial
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Basic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Polynomial
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Power
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Product
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Domain
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.NormalForm
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Affine
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Comparison
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.EventuallyGeometric


geometricTailDenominator : Real.ℝ → Real.ℝ → Real.ℝ
geometricTailDenominator ratio x =
  Real.ιℚ 1 Group.- (ratio Mul.· x)


geometricTailDenominatorDerivative :
  Real.ℝ → Real.ℝ → Real.ℝ
geometricTailDenominatorDerivative ratio x =
  Real.ιℚ 0 Group.-
    ((Real.ιℚ 0 Mul.· x) Add.+
      (ratio Mul.· Real.ιℚ 1))


geometricTailDenominatorHasDerivative : ∀ ratio →
  IsDerivative
    (geometricTailDenominator ratio)
    (geometricTailDenominatorDerivative ratio)
geometricTailDenominatorHasDerivative ratio =
  subHasDerivative
    (λ _ → Real.ιℚ 1)
    (λ x → ratio Mul.· x)
    (λ _ → Real.ιℚ 0)
    (λ x →
      (Real.ιℚ 0 Mul.· x) Add.+
        (ratio Mul.· Real.ιℚ 1))
    (constantHasDerivative (Real.ιℚ 1))
    (mulHasDerivative
      (λ _ → ratio) (idfun Real.ℝ)
      (λ _ → Real.ιℚ 0)
      (λ _ → Real.ιℚ 1)
      (constantHasDerivative ratio)
      identityHasDerivative)


polynomialGeometricTailNumerator :
  List Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
polynomialGeometricTailNumerator prefix coefficient x =
  coefficient Mul.· x ^ⁿ length prefix


polynomialGeometricTailNumeratorDerivative :
  List Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
polynomialGeometricTailNumeratorDerivative prefix coefficient x =
  (Real.ιℚ 0 Mul.· x ^ⁿ length prefix) Add.+
    (coefficient Mul.·
      naturalPowerDerivative (length prefix) x)


polynomialGeometricTailNumeratorHasDerivative :
  ∀ prefix coefficient →
  IsDerivative
    (polynomialGeometricTailNumerator prefix coefficient)
    (polynomialGeometricTailNumeratorDerivative prefix coefficient)
polynomialGeometricTailNumeratorHasDerivative prefix coefficient =
  mulHasDerivative
    (λ _ → coefficient)
    (λ x → x ^ⁿ length prefix)
    (λ _ → Real.ιℚ 0)
    (naturalPowerDerivative (length prefix))
    (constantHasDerivative coefficient)
    (naturalPowerHasDerivative (length prefix))


polynomialGeometricRationalNumerator :
  List Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
polynomialGeometricRationalNumerator
  prefix coefficient ratio x =
    (evaluatePolynomial prefix x Mul.·
      geometricTailDenominator ratio x) Add.+
    polynomialGeometricTailNumerator prefix coefficient x


polynomialGeometricRationalNumeratorDerivative :
  List Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
polynomialGeometricRationalNumeratorDerivative
  prefix coefficient ratio x =
    ((evaluatePolynomialDerivative prefix x Mul.·
        geometricTailDenominator ratio x) Add.+
      (evaluatePolynomial prefix x Mul.·
        geometricTailDenominatorDerivative ratio x)) Add.+
    polynomialGeometricTailNumeratorDerivative prefix coefficient x


polynomialGeometricRationalNumeratorHasDerivative :
  ∀ prefix coefficient ratio →
  IsDerivative
    (polynomialGeometricRationalNumerator
      prefix coefficient ratio)
    (polynomialGeometricRationalNumeratorDerivative
      prefix coefficient ratio)
polynomialGeometricRationalNumeratorHasDerivative
  prefix coefficient ratio =
    addHasDerivative
      (λ x →
        evaluatePolynomial prefix x Mul.·
          geometricTailDenominator ratio x)
      (polynomialGeometricTailNumerator prefix coefficient)
      (λ x →
        (evaluatePolynomialDerivative prefix x Mul.·
          geometricTailDenominator ratio x) Add.+
        (evaluatePolynomial prefix x Mul.·
          geometricTailDenominatorDerivative ratio x))
      (polynomialGeometricTailNumeratorDerivative prefix coefficient)
      (mulHasDerivative
        (evaluatePolynomial prefix)
        (geometricTailDenominator ratio)
        (evaluatePolynomialDerivative prefix)
        (geometricTailDenominatorDerivative ratio)
        (evaluatePolynomialHasDerivative prefix)
        (geometricTailDenominatorHasDerivative ratio))
      (polynomialGeometricTailNumeratorHasDerivative
        prefix coefficient)


PolynomialGeometricRationalDomain : Real.ℝ → Type
PolynomialGeometricRationalDomain ratio =
  ApartDenominatorDomain (geometricTailDenominator ratio)


polynomialGeometricRationalFunction :
  List Real.ℝ → Real.ℝ → ∀ ratio →
  PolynomialGeometricRationalDomain ratio → Real.ℝ
polynomialGeometricRationalFunction prefix coefficient ratio =
  divideOnApartDenominatorDomain
    (polynomialGeometricRationalNumerator
      prefix coefficient ratio)
    (geometricTailDenominator ratio)


polynomialGeometricRationalFunctionDerivative :
  List Real.ℝ → Real.ℝ → ∀ ratio →
  PolynomialGeometricRationalDomain ratio → Real.ℝ
polynomialGeometricRationalFunctionDerivative prefix coefficient ratio =
  divideOnApartDenominatorDomainDerivative
    (polynomialGeometricRationalNumerator
      prefix coefficient ratio)
    (geometricTailDenominator ratio)
    (polynomialGeometricRationalNumeratorDerivative
      prefix coefficient ratio)
    (geometricTailDenominatorDerivative ratio)


polynomialGeometricRationalFunctionConventionalDerivative :
  List Real.ℝ → Real.ℝ → ∀ ratio →
  PolynomialGeometricRationalDomain ratio → Real.ℝ
polynomialGeometricRationalFunctionConventionalDerivative
  prefix coefficient ratio =
    divideOnApartDenominatorDomainConventionalDerivative
      (polynomialGeometricRationalNumerator
        prefix coefficient ratio)
      (geometricTailDenominator ratio)
      (polynomialGeometricRationalNumeratorDerivative
        prefix coefficient ratio)
      (geometricTailDenominatorDerivative ratio)


polynomialGeometricRationalFunctionDerivative≡Conventional :
  ∀ prefix coefficient ratio →
  polynomialGeometricRationalFunctionDerivative
      prefix coefficient ratio
    ≡
  polynomialGeometricRationalFunctionConventionalDerivative
      prefix coefficient ratio
polynomialGeometricRationalFunctionDerivative≡Conventional
  prefix coefficient ratio =
    divideOnApartDenominatorDomainDerivative≡Conventional
      (polynomialGeometricRationalNumerator
        prefix coefficient ratio)
      (geometricTailDenominator ratio)
      (polynomialGeometricRationalNumeratorDerivative
        prefix coefficient ratio)
      (geometricTailDenominatorDerivative ratio)


polynomialGeometricRationalFunctionHasDerivativeAlong :
  ∀ prefix coefficient ratio →
  IsDerivativeAlong
    (snd
      (ApartDenominatorDomainPremetricSpace
        (geometricTailDenominator ratio)))
    apartDenominatorDomainCoordinate
    (polynomialGeometricRationalFunction
      prefix coefficient ratio)
    (polynomialGeometricRationalFunctionDerivative
      prefix coefficient ratio)
polynomialGeometricRationalFunctionHasDerivativeAlong
  prefix coefficient ratio =
    divideOnApartDenominatorDomainHasDerivativeAlong
      (polynomialGeometricRationalNumerator
        prefix coefficient ratio)
      (geometricTailDenominator ratio)
      (polynomialGeometricRationalNumeratorDerivative
        prefix coefficient ratio)
      (geometricTailDenominatorDerivative ratio)
      (polynomialGeometricRationalNumeratorHasDerivative
        prefix coefficient ratio)
      (geometricTailDenominatorHasDerivative ratio)


polynomialGeometricRationalFunctionHasConventionalDerivativeAlong :
  ∀ prefix coefficient ratio →
  IsDerivativeAlong
    (snd
      (ApartDenominatorDomainPremetricSpace
        (geometricTailDenominator ratio)))
    apartDenominatorDomainCoordinate
    (polynomialGeometricRationalFunction
      prefix coefficient ratio)
    (polynomialGeometricRationalFunctionConventionalDerivative
      prefix coefficient ratio)
polynomialGeometricRationalFunctionHasConventionalDerivativeAlong
  prefix coefficient ratio =
    divideOnApartDenominatorDomainHasConventionalDerivativeAlong
      (polynomialGeometricRationalNumerator
        prefix coefficient ratio)
      (geometricTailDenominator ratio)
      (polynomialGeometricRationalNumeratorDerivative
        prefix coefficient ratio)
      (geometricTailDenominatorDerivative ratio)
      (polynomialGeometricRationalNumeratorHasDerivative
        prefix coefficient ratio)
      (geometricTailDenominatorHasDerivative ratio)


geometricTailDenominatorPositive : ∀ ratio x →
  RationalContractionBound (ratio Mul.· x) →
  Real.ιℚ 0 <ℝ geometricTailDenominator ratio x
geometricTailDenominatorPositive ratio x contraction =
  strictlyPositiveDifference≪
    (ratio Mul.· x) (Real.ιℚ 1)
    (rationalContractionBound→x<1
      (ratio Mul.· x) contraction)


polynomialGeometricRationalDomainPoint : ∀ ratio x →
  RationalContractionBound (ratio Mul.· x) →
  PolynomialGeometricRationalDomain ratio
polynomialGeometricRationalDomainPoint ratio x contraction =
  x , inl (geometricTailDenominatorPositive ratio x contraction)


geometricTailRatioLessThanOneOfAbs<1 : ∀ ratio x →
  Abs.absℝ (ratio Mul.· x) <ℝ Real.ιℚ 1 →
  ratio Mul.· x <ℝ Real.ιℚ 1
geometricTailRatioLessThanOneOfAbs<1 ratio x abs-ratio-x<1 =
  ≤<ℝ-trans
    (ratio Mul.· x)
    (Abs.absℝ (ratio Mul.· x))
    (Real.ιℚ 1)
    (x≤abs (ratio Mul.· x))
    abs-ratio-x<1


geometricTailDenominatorPositiveOfAbs<1 : ∀ ratio x →
  Abs.absℝ (ratio Mul.· x) <ℝ Real.ιℚ 1 →
  Real.ιℚ 0 <ℝ geometricTailDenominator ratio x
geometricTailDenominatorPositiveOfAbs<1
  ratio x abs-ratio-x<1 =
    strictlyPositiveDifference≪
      (ratio Mul.· x) (Real.ιℚ 1)
      (geometricTailRatioLessThanOneOfAbs<1
        ratio x abs-ratio-x<1)


-- This domain point uses only the sharp open convergence condition.  No
-- rational contraction constant is selected from its truncated existence.

polynomialGeometricRationalDomainPointOfAbs<1 : ∀ ratio x →
  Abs.absℝ (ratio Mul.· x) <ℝ Real.ιℚ 1 →
  PolynomialGeometricRationalDomain ratio
polynomialGeometricRationalDomainPointOfAbs<1
  ratio x abs-ratio-x<1 =
    x , inl
      (geometricTailDenominatorPositiveOfAbs<1
        ratio x abs-ratio-x<1)


polynomialGeometricRationalFunction-expand :
  ∀ prefix coefficient ratio
    (point : PolynomialGeometricRationalDomain ratio) →
  polynomialGeometricRationalFunction
      prefix coefficient ratio point
    ≡
  evaluatePolynomial prefix (fst point) Add.+
    (polynomialGeometricTailNumerator
      prefix coefficient (fst point) Mul.·
      inverseℝ
        (geometricTailDenominator ratio (fst point))
        (snd point))
polynomialGeometricRationalFunction-expand
  prefix coefficient ratio point =
    mul-distrib-over-add-left
      (evaluatePolynomial prefix x Mul.·
        geometricTailDenominator ratio x)
      (polynomialGeometricTailNumerator prefix coefficient x)
      inverse
  ∙ cong
      (Add._+
        polynomialGeometricTailNumerator
          prefix coefficient x Mul.· inverse)
      ( sym
          (mul-assoc
            (evaluatePolynomial prefix x)
            (geometricTailDenominator ratio x)
            inverse)
      ∙ cong
          (evaluatePolynomial prefix x Mul.·_)
          (inverseℝLaw
            (geometricTailDenominator ratio x)
            (snd point))
      ∙ mul-one-right (evaluatePolynomial prefix x)
      )
  where
  x : Real.ℝ
  x = fst point

  inverse : Real.ℝ
  inverse =
    inverseℝ
      (geometricTailDenominator ratio x)
      (snd point)


polynomialGeometricRationalFunction-atContraction :
  ∀ prefix coefficient ratio x →
  (contraction : RationalContractionBound (ratio Mul.· x)) →
  polynomialGeometricRationalFunction
      prefix coefficient ratio
      (polynomialGeometricRationalDomainPoint
        ratio x contraction)
    ≡
  evaluatePolynomial prefix x Add.+
    ((coefficient Mul.· x ^ⁿ length prefix) Mul.·
      geometricReciprocal
        (ratio Mul.· x)
        (rationalContractionBound→x<1
          (ratio Mul.· x) contraction))
polynomialGeometricRationalFunction-atContraction
  prefix coefficient ratio x contraction =
    polynomialGeometricRationalFunction-expand
      prefix coefficient ratio
      (polynomialGeometricRationalDomainPoint
        ratio x contraction)


polynomialGeometricRationalFunction-atAbs<1 :
  ∀ prefix coefficient ratio x →
  (abs-ratio-x<1 :
    Abs.absℝ (ratio Mul.· x) <ℝ Real.ιℚ 1) →
  polynomialGeometricRationalFunction
      prefix coefficient ratio
      (polynomialGeometricRationalDomainPointOfAbs<1
        ratio x abs-ratio-x<1)
    ≡
  evaluatePolynomial prefix x Add.+
    ((coefficient Mul.· x ^ⁿ length prefix) Mul.·
      geometricReciprocal
        (ratio Mul.· x)
        (geometricTailRatioLessThanOneOfAbs<1
          ratio x abs-ratio-x<1))
polynomialGeometricRationalFunction-atAbs<1
  prefix coefficient ratio x abs-ratio-x<1 =
    polynomialGeometricRationalFunction-expand
      prefix coefficient ratio
      (polynomialGeometricRationalDomainPointOfAbs<1
        ratio x abs-ratio-x<1)


powerSeriesValue-polynomialGeometric≡rationalFunction :
  ∀ prefix coefficient ratio x →
  (contraction : RationalContractionBound (ratio Mul.· x)) →
  (summable :
    PowerSeriesSummableAt
      (polynomialGeometricCoefficients
        prefix coefficient ratio) x) →
  powerSeriesValue
      (polynomialGeometricCoefficients
        prefix coefficient ratio) x summable
    ≡
  polynomialGeometricRationalFunction
    prefix coefficient ratio
    (polynomialGeometricRationalDomainPoint
      ratio x contraction)
powerSeriesValue-polynomialGeometric≡rationalFunction
  prefix coefficient ratio x contraction summable =
    powerSeriesValue-polynomialGeometric
      prefix coefficient ratio x contraction summable
  ∙ sym
      (polynomialGeometricRationalFunction-atContraction
        prefix coefficient ratio x contraction)


-- The strongest bridge has no chosen convergence modulus in its interface.
-- The series proof consumes |ratio·x| < 1 propositionally, while that same
-- inequality supplies the positive denominator needed by the partial
-- rational function.

powerSeriesValue-polynomialGeometric≡rationalFunctionOfAbs<1 :
  ∀ prefix coefficient ratio x →
  (abs-ratio-x<1 :
    Abs.absℝ (ratio Mul.· x) <ℝ Real.ιℚ 1) →
  (summable :
    PowerSeriesSummableAt
      (polynomialGeometricCoefficients
        prefix coefficient ratio) x) →
  powerSeriesValue
      (polynomialGeometricCoefficients
        prefix coefficient ratio) x summable
    ≡
  polynomialGeometricRationalFunction
    prefix coefficient ratio
    (polynomialGeometricRationalDomainPointOfAbs<1
      ratio x abs-ratio-x<1)
powerSeriesValue-polynomialGeometric≡rationalFunctionOfAbs<1
  prefix coefficient ratio x abs-ratio-x<1 summable =
    powerSeriesValue-polynomialGeometricOfAbs<1
      prefix coefficient ratio x abs-ratio-x<1 summable
  ∙ sym
      (polynomialGeometricRationalFunction-atAbs<1
        prefix coefficient ratio x abs-ratio-x<1)
