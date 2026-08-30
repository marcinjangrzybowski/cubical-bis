module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Polynomial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals.Base
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Continuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Continuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Polynomial
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Chain
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Uniqueness


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


-- The derivative evaluator follows Horner's recurrence directly:
-- D(a + x p(x)) = p(x) + x Dp(x).

evaluatePolynomialDerivative :
  List Real.ℝ → Real.ℝ → Real.ℝ
evaluatePolynomialDerivative [] x = Real.ιℚ 0
evaluatePolynomialDerivative (a ∷ coefficients) x =
  evaluatePolynomial coefficients x Add.+
    (x Mul.· evaluatePolynomialDerivative coefficients x)


-- Weighting the tail by 1,2,3,... gives the usual formal derivative list.

weightPolynomialCoefficients :
  ℕ → List Real.ℝ → List Real.ℝ
weightPolynomialCoefficients n [] = []
weightPolynomialCoefficients n (coefficient ∷ coefficients) =
  (realNatural n Mul.· coefficient) ∷
    weightPolynomialCoefficients (suc n) coefficients


polynomialDerivativeCoefficients :
  List Real.ℝ → List Real.ℝ
polynomialDerivativeCoefficients [] = []
polynomialDerivativeCoefficients (constant ∷ coefficients) =
  weightPolynomialCoefficients (suc zero) coefficients


private
  commuteWeightedProduct :
    ∀ (a b c : Real.ℝ) →
    a Mul.· (b Mul.· c) ≡ b Mul.· (a Mul.· c)
  commuteWeightedProduct a b c =
    mul-assoc a b c
    ∙ cong (Mul._· c) (mul-comm a b)
    ∙ sym (mul-assoc b a c)

  weightedPolynomialStep :
    ∀ (n coefficient x tail derivative-tail : Real.ℝ) →
    (n Mul.· coefficient) Add.+
        (x Mul.·
          (((n Add.+ Real.ιℚ 1) Mul.· tail) Add.+
            (x Mul.· derivative-tail)))
      ≡
    (n Mul.· (coefficient Add.+ (x Mul.· tail))) Add.+
      (x Mul.· (tail Add.+ (x Mul.· derivative-tail)))
  weightedPolynomialStep
    n coefficient x tail derivative-tail =
      cong
        ((n Mul.· coefficient) Add.+_)
        (cong
          (x Mul.·_)
          (cong
            (Add._+ (x Mul.· derivative-tail))
            (mul-distrib-over-add-left n (Real.ιℚ 1) tail
            ∙ cong ((n Mul.· tail) Add.+_)
                (mul-one-left tail))))
    ∙ cong
        ((n Mul.· coefficient) Add.+_)
        (mul-distrib-over-add-right
          x ((n Mul.· tail) Add.+ tail)
          (x Mul.· derivative-tail))
    ∙ cong
        ((n Mul.· coefficient) Add.+_)
        (cong
          (Add._+ (x Mul.· (x Mul.· derivative-tail)))
          (mul-distrib-over-add-right x (n Mul.· tail) tail))
    ∙ add-assoc
        (n Mul.· coefficient)
        ((x Mul.· (n Mul.· tail)) Add.+ (x Mul.· tail))
        (x Mul.· (x Mul.· derivative-tail))
    ∙ cong
        (Add._+ (x Mul.· (x Mul.· derivative-tail)))
        (add-assoc
          (n Mul.· coefficient)
          (x Mul.· (n Mul.· tail))
          (x Mul.· tail))
    ∙ cong
        (λ value →
          (((n Mul.· coefficient) Add.+ value) Add.+
            (x Mul.· tail)) Add.+
          (x Mul.· (x Mul.· derivative-tail)))
        (commuteWeightedProduct x n tail)
    ∙ sym
        (add-assoc
          ((n Mul.· coefficient) Add.+
            (n Mul.· (x Mul.· tail)))
          (x Mul.· tail)
          (x Mul.· (x Mul.· derivative-tail)))
    ∙ cong₂ Add._+_
        (sym
          (mul-distrib-over-add-right
            n coefficient (x Mul.· tail)))
        (sym
          (mul-distrib-over-add-right
            x tail (x Mul.· derivative-tail)))


weightPolynomialEvaluation :
  ∀ n coefficients x →
  evaluatePolynomial
      (weightPolynomialCoefficients n coefficients) x
    ≡
  (realNatural n Mul.· evaluatePolynomial coefficients x) Add.+
    (x Mul.· evaluatePolynomialDerivative coefficients x)
weightPolynomialEvaluation n [] x =
  sym
    (cong₂ Add._+_
      (mul-zero-right (realNatural n))
      (mul-zero-right x)
    ∙ add-zero-left (Real.ιℚ 0))
weightPolynomialEvaluation n (coefficient ∷ coefficients) x =
  cong
      (λ value →
        (realNatural n Mul.· coefficient) Add.+
          (x Mul.· value))
      (weightPolynomialEvaluation (suc n) coefficients x)
  ∙ cong
      ((realNatural n Mul.· coefficient) Add.+_)
      (cong
        (x Mul.·_)
        (cong
          (λ value →
            (value Mul.· evaluatePolynomial coefficients x) Add.+
              (x Mul.·
                evaluatePolynomialDerivative coefficients x))
          (realNatural-suc n)))
  ∙ weightedPolynomialStep
      (realNatural n) coefficient x
      (evaluatePolynomial coefficients x)
      (evaluatePolynomialDerivative coefficients x)


evaluatePolynomialDerivativeCoefficients :
  ∀ coefficients x →
  evaluatePolynomial
      (polynomialDerivativeCoefficients coefficients) x
    ≡
  evaluatePolynomialDerivative coefficients x
evaluatePolynomialDerivativeCoefficients [] x = refl
evaluatePolynomialDerivativeCoefficients
  (constant ∷ coefficients) x =
    weightPolynomialEvaluation (suc zero) coefficients x
    ∙ cong
        (Add._+ (x Mul.·
          evaluatePolynomialDerivative coefficients x))
        (cong
          (Mul._· evaluatePolynomial coefficients x)
          (realNatural-suc zero
          ∙ add-zero-left (realNatural (suc zero)))
        ∙ mul-one-left
            (evaluatePolynomial coefficients x))


-- A division-free two-point polynomial.  It specializes to the derivative
-- evaluator on the diagonal and factors every finite difference.

evaluatePolynomialDifferenceFactor :
  List Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
evaluatePolynomialDifferenceFactor [] x y = Real.ιℚ 0
evaluatePolynomialDifferenceFactor (a ∷ coefficients) x y =
  evaluatePolynomial coefficients y Add.+
    (x Mul.·
      evaluatePolynomialDifferenceFactor coefficients x y)


private
  hornerForwardDifferencePath :
    ∀ (a x y p q : Real.ℝ) →
    ((a Add.+ (y Mul.· p)) Group.-
        (a Add.+ (x Mul.· q)))
      ≡
    ((y Group.- x) Mul.· p) Add.+
      (x Mul.· (p Group.- q))
  hornerForwardDifferencePath a x y p q =
    sym
      (ℝRing.translatedDifference
        a (y Mul.· p) (x Mul.· q))
    ∙ product-difference
    where
    yp : Real.ℝ
    yp = y Mul.· p

    xp : Real.ℝ
    xp = x Mul.· p

    xq : Real.ℝ
    xq = x Mul.· q

    product-difference :
      yp Group.- xq
        ≡
      ((y Group.- x) Mul.· p) Add.+
        (x Mul.· (p Group.- q))
    product-difference =
      cong (yp Add.+_)
        (sym (add-zero-left (Neg.- xq)))
      ∙ cong
          (λ value → yp Add.+ (value Add.+ (Neg.- xq)))
          (sym (add-inverse-left xp))
      ∙ add-assoc yp ((Neg.- xp) Add.+ xp) (Neg.- xq)
      ∙ cong (Add._+ (Neg.- xq))
          (add-assoc yp (Neg.- xp) xp)
      ∙ sym
          (add-assoc
            (yp Add.+ (Neg.- xp)) xp (Neg.- xq))
      ∙ cong₂ Add._+_
          (sym (ℝRing.·DistL- y x p))
          (sym (ℝRing.·DistR- x p q))

  commuteNestedProduct :
    ∀ (a b c : Real.ℝ) →
    a Mul.· (b Mul.· c) ≡ b Mul.· (a Mul.· c)
  commuteNestedProduct a b c =
    mul-assoc a b c
    ∙ cong (Mul._· c) (mul-comm a b)
    ∙ sym (mul-assoc b a c)


evaluatePolynomialDifferenceFactorization :
  ∀ coefficients x y →
  evaluatePolynomial coefficients y Group.-
      evaluatePolynomial coefficients x
    ≡
  (y Group.- x) Mul.·
    evaluatePolynomialDifferenceFactor coefficients x y
evaluatePolynomialDifferenceFactorization [] x y =
  sub-self (Real.ιℚ 0)
  ∙ sym (mul-zero-right (y Group.- x))
evaluatePolynomialDifferenceFactorization
  (a ∷ coefficients) x y =
    hornerForwardDifferencePath a x y tail-y tail-x
    ∙ cong
        (((y Group.- x) Mul.· tail-y) Add.+_)
        (cong (x Mul.·_)
          (evaluatePolynomialDifferenceFactorization
            coefficients x y))
    ∙ cong
        (((y Group.- x) Mul.· tail-y) Add.+_)
        (commuteNestedProduct
          x (y Group.- x) factor)
    ∙ sym
        (mul-distrib-over-add-right
          (y Group.- x) tail-y (x Mul.· factor))
  where
  tail-x : Real.ℝ
  tail-x = evaluatePolynomial coefficients x

  tail-y : Real.ℝ
  tail-y = evaluatePolynomial coefficients y

  factor : Real.ℝ
  factor =
    evaluatePolynomialDifferenceFactor coefficients x y


evaluatePolynomialDifferenceFactorDiagonal :
  ∀ coefficients x →
  evaluatePolynomialDifferenceFactor coefficients x x
    ≡
  evaluatePolynomialDerivative coefficients x
evaluatePolynomialDifferenceFactorDiagonal [] x = refl
evaluatePolynomialDifferenceFactorDiagonal
  (a ∷ coefficients) x =
    cong
      (λ value →
        evaluatePolynomial coefficients x Add.+
          (x Mul.· value))
      (evaluatePolynomialDifferenceFactorDiagonal coefficients x)


-- Horner evaluation and its two-point factor preserve continuity without
-- choosing a global modulus: each finite recursive step combines only the
-- propositionally truncated local witnesses it needs.

evaluatePolynomialOfContinuousIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → Real.ℝ) →
  isContinuous source coordinate
    (snd Real.ℝPremetricSpace) →
  ∀ coefficients →
  isContinuous source
    (λ point → evaluatePolynomial coefficients (coordinate point))
    (snd Real.ℝPremetricSpace)
evaluatePolynomialOfContinuousIsContinuous
  source coordinate coordinate-continuous [] point
  .IsContinuousAt.pres≈ ε =
    return
      ( ε
      , λ _ _ → Real.Base.isRefl≈ᶜ (Real.ιℚ 0) ε
      )
evaluatePolynomialOfContinuousIsContinuous
  source coordinate coordinate-continuous
  (a ∷ coefficients) =
    addOfContinuousIsContinuous
      source
      (λ _ → a)
      (λ point →
        coordinate point Mul.·
          evaluatePolynomial coefficients (coordinate point))
      constant-continuous
      (mulOfContinuousIsContinuous
        source coordinate
        (λ point → evaluatePolynomial coefficients (coordinate point))
        coordinate-continuous
        (evaluatePolynomialOfContinuousIsContinuous
          source coordinate coordinate-continuous coefficients))
  where
  constant-continuous :
    isContinuous source (λ _ → a) (snd Real.ℝPremetricSpace)
  constant-continuous point .IsContinuousAt.pres≈ ε =
    return
      ( ε
      , λ _ _ → Real.Base.isRefl≈ᶜ a ε
      )


evaluatePolynomialDifferenceFactorOfContinuousIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (x y : A → Real.ℝ) →
  isContinuous source x (snd Real.ℝPremetricSpace) →
  isContinuous source y (snd Real.ℝPremetricSpace) →
  ∀ coefficients →
  isContinuous source
    (λ point →
      evaluatePolynomialDifferenceFactor
        coefficients (x point) (y point))
    (snd Real.ℝPremetricSpace)
evaluatePolynomialDifferenceFactorOfContinuousIsContinuous
  source x y x-continuous y-continuous [] point
  .IsContinuousAt.pres≈ ε =
    return
      ( ε
      , λ _ _ → Real.Base.isRefl≈ᶜ (Real.ιℚ 0) ε
      )
evaluatePolynomialDifferenceFactorOfContinuousIsContinuous
  source x y x-continuous y-continuous
  (a ∷ coefficients) =
    addOfContinuousIsContinuous
      source
      (λ point → evaluatePolynomial coefficients (y point))
      (λ point →
        x point Mul.·
          evaluatePolynomialDifferenceFactor
            coefficients (x point) (y point))
      (evaluatePolynomialOfContinuousIsContinuous
        source y y-continuous coefficients)
      (mulOfContinuousIsContinuous
        source x
        (λ point →
          evaluatePolynomialDifferenceFactor
            coefficients (x point) (y point))
        x-continuous
        (evaluatePolynomialDifferenceFactorOfContinuousIsContinuous
          source x y x-continuous y-continuous coefficients))


private
  realPairPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
  realPairPremetricSpace =
    PremetricProduct Real.ℝPremetricSpace Real.ℝPremetricSpace

  pairLeftIsContinuous :
    isContinuous
      (snd realPairPremetricSpace) fst
      (snd Real.ℝPremetricSpace)
  pairLeftIsContinuous =
    snd
      (productFstC
        {M = Real.ℝPremetricSpace}
        {N = Real.ℝPremetricSpace})

  pairRightIsContinuous :
    isContinuous
      (snd realPairPremetricSpace) snd
      (snd Real.ℝPremetricSpace)
  pairRightIsContinuous =
    snd
      (productSndC
        {M = Real.ℝPremetricSpace}
        {N = Real.ℝPremetricSpace})


evaluatePolynomialDifferenceFactorIsContinuous :
  ∀ coefficients →
  isContinuous
    (snd realPairPremetricSpace)
    (λ point →
      evaluatePolynomialDifferenceFactor
        coefficients (fst point) (snd point))
    (snd Real.ℝPremetricSpace)
evaluatePolynomialDifferenceFactorIsContinuous coefficients =
  evaluatePolynomialDifferenceFactorOfContinuousIsContinuous
    (snd realPairPremetricSpace)
    fst snd pairLeftIsContinuous pairRightIsContinuous
    coefficients


evaluatePolynomialOfContinuousHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → Real.ℝ) →
  isContinuous source coordinate
    (snd Real.ℝPremetricSpace) →
  ∀ coefficients →
  IsDerivativeAlong
    source coordinate
    (λ point →
      evaluatePolynomial coefficients (coordinate point))
    (λ point →
      evaluatePolynomialDerivative coefficients (coordinate point))
evaluatePolynomialOfContinuousHasDerivativeAlong
  {ℓ = ℓ} {ℓ' = ℓ'} {A = A}
  source coordinate coordinate-continuous coefficients =
    continuousDifferenceFactorGivesDerivative
      source coordinate
      (λ point →
        evaluatePolynomial coefficients (coordinate point))
      (λ point →
        evaluatePolynomialDerivative coefficients (coordinate point))
      (λ points →
        evaluatePolynomialDifferenceFactor coefficients
          (coordinate (fst points))
          (coordinate (snd points)))
      (λ x y →
        evaluatePolynomialDifferenceFactorization
          coefficients (coordinate x) (coordinate y))
      (λ x →
        evaluatePolynomialDifferenceFactorDiagonal
          coefficients (coordinate x))
      (evaluatePolynomialDifferenceFactorOfContinuousIsContinuous
        (PremetricProductStr source source)
        (coordinate ∘ fst) (coordinate ∘ snd)
        (snd left-coordinate) (snd right-coordinate)
        coefficients)
  where
  source-space : PremetricSpace ℓ ℓ'
  source-space = A , source

  open CategoryStructures

  left-coordinate :
    C[
      PremetricProduct source-space source-space
      , Real.ℝPremetricSpace
    ]
  left-coordinate =
    (coordinate , coordinate-continuous) ∘C productFstC

  right-coordinate :
    C[
      PremetricProduct source-space source-space
      , Real.ℝPremetricSpace
    ]
  right-coordinate =
    (coordinate , coordinate-continuous) ∘C productSndC


evaluatePolynomialHasDerivative :
  ∀ coefficients →
  IsDerivative
    (evaluatePolynomial coefficients)
    (evaluatePolynomialDerivative coefficients)
evaluatePolynomialHasDerivative coefficients =
  evaluatePolynomialOfContinuousHasDerivativeAlong
    (snd Real.ℝPremetricSpace)
    (idfun Real.ℝ)
    (snd
      (CategoryStructures.idᶜ
        {M = Real.ℝPremetricSpace}))
    coefficients


evaluatePolynomialFormalDerivativeHasDerivative :
  ∀ coefficients →
  IsDerivative
    (evaluatePolynomial coefficients)
    (evaluatePolynomial
      (polynomialDerivativeCoefficients coefficients))
evaluatePolynomialFormalDerivativeHasDerivative coefficients =
  subst
    (IsDerivative (evaluatePolynomial coefficients))
    (sym
      (funExt
        (evaluatePolynomialDerivativeCoefficients coefficients)))
    (evaluatePolynomialHasDerivative coefficients)


evaluatePolynomialCompositionHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate inner inner' : A → Real.ℝ) →
  isContinuous source coordinate
    (snd Real.ℝPremetricSpace) →
  IsDerivativeAlong source coordinate inner inner' →
  ∀ coefficients →
  IsDerivativeAlong
    source coordinate
    (λ point → evaluatePolynomial coefficients (inner point))
    (λ point →
      evaluatePolynomialDerivative coefficients (inner point) Mul.·
        inner' point)
evaluatePolynomialCompositionHasDerivativeAlong
  source coordinate inner inner'
  coordinate-continuous inner-derivative coefficients =
    chainHasDerivativeAlong
      source coordinate inner inner'
      (evaluatePolynomial coefficients)
      (evaluatePolynomialDerivative coefficients)
      coordinate-continuous inner-derivative
      (evaluatePolynomialHasDerivative coefficients)


evaluatePolynomialCompositionHasDerivative :
  ∀ inner inner' coefficients →
  IsDerivative inner inner' →
  IsDerivative
    (λ x → evaluatePolynomial coefficients (inner x))
    (λ x →
      evaluatePolynomialDerivative coefficients (inner x) Mul.·
        inner' x)
evaluatePolynomialCompositionHasDerivative
  inner inner' coefficients inner-derivative =
    chainHasDerivative
      inner inner'
      (evaluatePolynomial coefficients)
      (evaluatePolynomialDerivative coefficients)
      inner-derivative
      (evaluatePolynomialHasDerivative coefficients)


evaluatePolynomialDerivativeUnique :
  ∀ coefficients derivative →
  IsDerivative (evaluatePolynomial coefficients) derivative →
  derivative ≡ evaluatePolynomialDerivative coefficients
evaluatePolynomialDerivativeUnique
  coefficients derivative has-derivative =
    derivativeFunctionUnique
      (evaluatePolynomial coefficients)
      derivative
      (evaluatePolynomialDerivative coefficients)
      has-derivative
      (evaluatePolynomialHasDerivative coefficients)


evaluatePolynomialDerivativeValueUnique :
  ∀ coefficients x derivative-value →
  IsDerivativeAt
    (evaluatePolynomial coefficients) derivative-value x →
  derivative-value ≡ evaluatePolynomialDerivative coefficients x
evaluatePolynomialDerivativeValueUnique
  coefficients x derivative-value has-derivative =
    derivativeValueUniqueAt
      (evaluatePolynomial coefficients)
      x derivative-value
      (evaluatePolynomialDerivative coefficients x)
      has-derivative
      (isDerivativeAt
        (evaluatePolynomial coefficients)
        (evaluatePolynomialDerivative coefficients)
        (evaluatePolynomialHasDerivative coefficients)
        x)
