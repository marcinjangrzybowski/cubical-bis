module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Rationals.Base

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

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
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (abs-triangle ; add-monotone)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (abs-mul ; mul-monotone-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Majorant
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  oneℝ : Real.ℝ
  oneℝ = Real.ιℚ 1

  productDifferencePath :
    ∀ x y p q →
    (x Mul.· p) Group.- (y Mul.· q)
      ≡
    ((x Group.- y) Mul.· p) Add.+
      (y Mul.· (p Group.- q))
  productDifferencePath x y p q =
      cong (xp Add.+_)
        (sym (add-zero-left (Neg.- yq)))
    ∙ cong (λ z → xp Add.+ (z Add.+ (Neg.- yq)))
        (sym (add-inverse-left yp))
    ∙ add-assoc xp ((Neg.- yp) Add.+ yp) (Neg.- yq)
    ∙ cong (Add._+ (Neg.- yq))
        (add-assoc xp (Neg.- yp) yp)
    ∙ sym
        (add-assoc
          (xp Add.+ (Neg.- yp)) yp (Neg.- yq))
    ∙ cong₂ Add._+_
        (sym (ℝRing.·DistL- x y p))
        (sym (ℝRing.·DistR- y p q))
    where
    xp : Real.ℝ
    xp = x Mul.· p

    yp : Real.ℝ
    yp = y Mul.· p

    yq : Real.ℝ
    yq = y Mul.· q


  differenceOfSums :
    ∀ a b c d →
    (a Add.+ b) Group.- (c Add.+ d)
      ≡
    (a Group.- c) Add.+ (b Group.- d)
  differenceOfSums a b c d =
      cong ((a Add.+ b) Add.+_) (neg-add c d)
    ∙ sym (add-assoc a b ((Neg.- c) Add.+ (Neg.- d)))
    ∙ cong (a Add.+_)
        (add-assoc b (Neg.- c) (Neg.- d))
    ∙ cong (λ z → a Add.+ (z Add.+ (Neg.- d)))
        (add-comm b (Neg.- c))
    ∙ cong (a Add.+_)
        (sym (add-assoc (Neg.- c) b (Neg.- d)))
    ∙ add-assoc a (Neg.- c) (b Add.+ (Neg.- d))


  commuteNestedProduct :
    ∀ a b c →
    a Mul.· (b Mul.· c) ≡ b Mul.· (a Mul.· c)
  commuteNestedProduct a b c =
      mul-assoc a b c
    ∙ cong (Mul._· c) (mul-comm a b)
    ∙ sym (mul-assoc b a c)


  collectSuccessorMultiple :
    ∀ coefficient value →
    value Add.+ (coefficient Mul.· value)
      ≡
    (coefficient Add.+ oneℝ) Mul.· value
  collectSuccessorMultiple coefficient value =
      cong (Add._+ (coefficient Mul.· value))
        (sym (mul-one-left value))
    ∙ add-comm
        (oneℝ Mul.· value)
        (coefficient Mul.· value)
    ∙ sym
        (mul-distrib-over-add-left coefficient oneℝ value)


-- The divided-difference polynomial for the power with exponent `suc n`.
-- No division by `y - x` is used, so the same expression is meaningful and
-- continuous on the diagonal.

powerDifferenceFactor :
  Real.ℝ → Real.ℝ → ℕ → Real.ℝ
powerDifferenceFactor x y zero = oneℝ
powerDifferenceFactor x y (suc n) =
  (y ^ⁿ suc n) Add.+
    (x Mul.· powerDifferenceFactor x y n)


powerDifferenceFactor-identity :
  ∀ x y n →
  (y ^ⁿ suc n) Group.- (x ^ⁿ suc n)
    ≡
  (y Group.- x) Mul.· powerDifferenceFactor x y n
powerDifferenceFactor-identity x y zero =
    cong₂ Group._-_
      (mul-one-right y)
      (mul-one-right x)
  ∙ sym (mul-one-right (y Group.- x))
powerDifferenceFactor-identity x y (suc n) =
    productDifferencePath
      y x (y ^ⁿ suc n) (x ^ⁿ suc n)
  ∙ cong
      (((y Group.- x) Mul.· (y ^ⁿ suc n)) Add.+_)
      (cong (x Mul.·_)
        (powerDifferenceFactor-identity x y n))
  ∙ cong
      (((y Group.- x) Mul.· (y ^ⁿ suc n)) Add.+_)
      (commuteNestedProduct
        x (y Group.- x) (powerDifferenceFactor x y n))
  ∙ sym
      (mul-distrib-over-add-right
        (y Group.- x)
        (y ^ⁿ suc n)
        (x Mul.· powerDifferenceFactor x y n))


powerDifferenceFactor-diagonal :
  ∀ x n →
  powerDifferenceFactor x x n
    ≡
  realNatural (suc n) Mul.· x ^ⁿ n
powerDifferenceFactor-diagonal x zero =
    sym realNatural-one
  ∙ sym (mul-one-right (realNatural (suc zero)))
powerDifferenceFactor-diagonal x (suc n) =
    cong
      (λ value → (x ^ⁿ suc n) Add.+ (x Mul.· value))
      (powerDifferenceFactor-diagonal x n)
  ∙ cong
      ((x ^ⁿ suc n) Add.+_)
      (commuteNestedProduct
        x (realNatural (suc n)) (x ^ⁿ n))
  ∙ collectSuccessorMultiple
      (realNatural (suc n)) (x ^ⁿ suc n)
  ∙ cong (Mul._· (x ^ⁿ suc n))
      (cong (realNatural (suc n) Add.+_) (sym realNatural-one)
      ∙ sym (realNatural-suc (suc n)))


powerDifferenceFactorOfContinuousIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (x y : A → Real.ℝ) →
  isContinuous source x (snd Real.ℝPremetricSpace) →
  isContinuous source y (snd Real.ℝPremetricSpace) →
  ∀ n →
  isContinuous source
    (λ point →
      powerDifferenceFactor (x point) (y point) n)
    (snd Real.ℝPremetricSpace)
powerDifferenceFactorOfContinuousIsContinuous
  source x y x-continuous y-continuous zero point
  .IsContinuousAt.pres≈ ε =
  return
    ( ε
    , λ _ _ → Real.Base.isRefl≈ᶜ oneℝ ε
    )
powerDifferenceFactorOfContinuousIsContinuous
  source x y x-continuous y-continuous (suc n) =
  addOfContinuousIsContinuous
    source
    (λ point → y point ^ⁿ suc n)
    (λ point →
      x point Mul.· powerDifferenceFactor (x point) (y point) n)
    (powerOfContinuousIsContinuous
      source y y-continuous (suc n))
    (mulOfContinuousIsContinuous
      source x
      (λ point → powerDifferenceFactor (x point) (y point) n)
      x-continuous
      (powerDifferenceFactorOfContinuousIsContinuous
        source x y x-continuous y-continuous n))


powerDifferenceFactor-bound :
  ∀ x y radius →
  Real.ιℚ 0 ≤ℝ radius →
  Abs.absℝ x ≤ℝ radius →
  Abs.absℝ y ≤ℝ radius →
  ∀ n →
  Abs.absℝ (powerDifferenceFactor x y n)
    ≤ℝ
  realNatural (suc n) Mul.· radius ^ⁿ n
powerDifferenceFactor-bound
  x y radius 0≤radius absx≤radius absy≤radius zero =
  subst
    (_≤ℝ (realNatural (suc zero) Mul.· radius ^ⁿ zero))
    (sym absOne)
    (subst
      (oneℝ ≤ℝ_)
      (sym target-is-one)
      (≤ℝ-refl oneℝ))
  where
  target-is-one :
    realNatural (suc zero) Mul.· radius ^ⁿ zero ≡ oneℝ
  target-is-one =
      cong (Mul._· oneℝ) realNatural-one
    ∙ mul-one-right oneℝ
powerDifferenceFactor-bound
  x y radius 0≤radius absx≤radius absy≤radius (suc n) =
  ≤ℝ-trans
    (Abs.absℝ
      ((y ^ⁿ suc n) Add.+
        (x Mul.· powerDifferenceFactor x y n)))
    (Abs.absℝ (y ^ⁿ suc n) Add.+
      Abs.absℝ (x Mul.· powerDifferenceFactor x y n))
    (realNatural (suc (suc n)) Mul.· radius ^ⁿ suc n)
    (abs-triangle
      (y ^ⁿ suc n)
      (x Mul.· powerDifferenceFactor x y n))
    (subst
      ((Abs.absℝ (y ^ⁿ suc n) Add.+
        Abs.absℝ (x Mul.· powerDifferenceFactor x y n)) ≤ℝ_)
      sum-bound-path
      (add-monotone
        (Abs.absℝ (y ^ⁿ suc n))
        (radius ^ⁿ suc n)
        (Abs.absℝ (x Mul.· powerDifferenceFactor x y n))
        (radius Mul.·
          (realNatural (suc n) Mul.· radius ^ⁿ n))
        power-bound product-bound))
  where
  power-bound :
    Abs.absℝ (y ^ⁿ suc n) ≤ℝ radius ^ⁿ suc n
  power-bound =
    subst
      (_≤ℝ radius ^ⁿ suc n)
      (sym (absPow (suc n) y))
      (powMono (suc n) (zero≤abs y) absy≤radius)

  product-bound :
    Abs.absℝ (x Mul.· powerDifferenceFactor x y n)
      ≤ℝ
    radius Mul.·
      (realNatural (suc n) Mul.· radius ^ⁿ n)
  product-bound =
    subst
      (_≤ℝ
        (radius Mul.·
          (realNatural (suc n) Mul.· radius ^ⁿ n)))
      (sym (abs-mul x (powerDifferenceFactor x y n)))
      (mul-monotone-nonnegative
        (Abs.absℝ x) radius
        (Abs.absℝ (powerDifferenceFactor x y n))
        (realNatural (suc n) Mul.· radius ^ⁿ n)
        absx≤radius
        (powerDifferenceFactor-bound
          x y radius 0≤radius absx≤radius absy≤radius n)
        (zero≤abs x)
        (zero≤abs (powerDifferenceFactor x y n)))

  sum-bound-path :
    (radius ^ⁿ suc n) Add.+
        (radius Mul.·
          (realNatural (suc n) Mul.· radius ^ⁿ n))
      ≡
    realNatural (suc (suc n)) Mul.· radius ^ⁿ suc n
  sum-bound-path =
      cong ((radius ^ⁿ suc n) Add.+_)
        (commuteNestedProduct
          radius (realNatural (suc n)) (radius ^ⁿ n))
    ∙ collectSuccessorMultiple
        (realNatural (suc n)) (radius ^ⁿ suc n)
    ∙ cong (Mul._· (radius ^ⁿ suc n))
        (cong (realNatural (suc n) Add.+_) (sym realNatural-one)
        ∙ sym (realNatural-suc (suc n)))


powerSeriesDifferenceFactor :
  RealSequence → Real.ℝ → Real.ℝ → RealSequence
powerSeriesDifferenceFactor coefficients x y n =
  coefficients (suc n) Mul.· powerDifferenceFactor x y n


-- Coefficient majorization already contains nonnegativity of the majorant,
-- so the bound does not ask callers to repeat that premise.

powerSeriesDifferenceFactorTermBoundByDerivativeMajorant :
  ∀ coefficients majorant x y radius →
  CoefficientMajorizedBy coefficients majorant →
  Real.ιℚ 0 ≤ℝ radius →
  Abs.absℝ x ≤ℝ radius →
  Abs.absℝ y ≤ℝ radius →
  ∀ n →
  Abs.absℝ
      (powerSeriesDifferenceFactor coefficients x y n)
    ≤ℝ
  powerSeriesTerms
    (formalDerivativeMajorant majorant) radius n
powerSeriesDifferenceFactorTermBoundByDerivativeMajorant
  coefficients majorant x y radius
  majorized 0≤radius absx≤radius absy≤radius n =
  subst2 _≤ℝ_
    (sym
      (abs-mul
        (coefficients (suc n))
        (powerDifferenceFactor x y n)))
    target-path
    (mul-monotone-nonnegative
      (Abs.absℝ (coefficients (suc n)))
      (majorant (suc n))
      (Abs.absℝ (powerDifferenceFactor x y n))
      (realNatural (suc n) Mul.· radius ^ⁿ n)
      (majorized (suc n))
      (powerDifferenceFactor-bound
        x y radius 0≤radius absx≤radius absy≤radius n)
      (zero≤abs (coefficients (suc n)))
      (zero≤abs (powerDifferenceFactor x y n)))
  where
  target-path :
    majorant (suc n) Mul.·
        (realNatural (suc n) Mul.· radius ^ⁿ n)
      ≡
    powerSeriesTerms
      (formalDerivativeMajorant majorant) radius n
  target-path =
      commuteNestedProduct
        (majorant (suc n))
        (realNatural (suc n))
        (radius ^ⁿ n)
    ∙ mul-assoc
        (realNatural (suc n))
        (majorant (suc n))
        (radius ^ⁿ n)


powerSeriesDifferenceFactorOfContinuousIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    coefficients
    (x y : A → Real.ℝ) →
  isContinuous source x (snd Real.ℝPremetricSpace) →
  isContinuous source y (snd Real.ℝPremetricSpace) →
  ∀ n →
  isContinuous source
    (λ point →
      powerSeriesDifferenceFactor
        coefficients (x point) (y point) n)
    (snd Real.ℝPremetricSpace)
powerSeriesDifferenceFactorOfContinuousIsContinuous
  source coefficients x y x-continuous y-continuous n =
  mulOfContinuousIsContinuous
    source
    (λ _ → coefficients (suc n))
    (λ point → powerDifferenceFactor (x point) (y point) n)
    constant-continuous
    (powerDifferenceFactorOfContinuousIsContinuous
      source x y x-continuous y-continuous n)
  where
  constant-continuous :
    isContinuous source
      (λ _ → coefficients (suc n))
      (snd Real.ℝPremetricSpace)
  constant-continuous point .IsContinuousAt.pres≈ ε =
    return
      ( ε
      , λ _ _ → Real.Base.isRefl≈ᶜ (coefficients (suc n)) ε
      )


powerSeriesDifferenceFactor-diagonal :
  ∀ coefficients x →
  powerSeriesDifferenceFactor coefficients x x
    ≡
  powerSeriesTerms (formalDerivative coefficients) x
powerSeriesDifferenceFactor-diagonal coefficients x =
  funExt λ n →
      cong (coefficients (suc n) Mul.·_)
        (powerDifferenceFactor-diagonal x n)
    ∙ commuteNestedProduct
        (coefficients (suc n))
        (realNatural (suc n))
        (x ^ⁿ n)
    ∙ mul-assoc
        (realNatural (suc n))
        (coefficients (suc n))
        (x ^ⁿ n)


finitePowerSeriesDifference :
  ∀ coefficients x y n →
  partialSum (powerSeriesTerms coefficients y) (suc n) Group.-
    partialSum (powerSeriesTerms coefficients x) (suc n)
    ≡
  (y Group.- x) Mul.·
    partialSum (powerSeriesDifferenceFactor coefficients x y) n
finitePowerSeriesDifference coefficients x y zero =
    cong₂ Group._-_
      (add-zero-left (coefficients zero Mul.· y ^ⁿ zero)
      ∙ mul-one-right (coefficients zero))
      (add-zero-left (coefficients zero Mul.· x ^ⁿ zero)
      ∙ mul-one-right (coefficients zero))
  ∙ sub-self (coefficients zero)
  ∙ sym (mul-zero-right (y Group.- x))
finitePowerSeriesDifference coefficients x y (suc n) =
    differenceOfSums
      (partialSum (powerSeriesTerms coefficients y) (suc n))
      (powerSeriesTerms coefficients y (suc n))
      (partialSum (powerSeriesTerms coefficients x) (suc n))
      (powerSeriesTerms coefficients x (suc n))
  ∙ cong₂ Add._+_
      (finitePowerSeriesDifference coefficients x y n)
      term-difference
  ∙ sym
      (mul-distrib-over-add-right
        (y Group.- x)
        (partialSum (powerSeriesDifferenceFactor coefficients x y) n)
        (powerSeriesDifferenceFactor coefficients x y n))
  where
  term-difference :
    powerSeriesTerms coefficients y (suc n) Group.-
      powerSeriesTerms coefficients x (suc n)
      ≡
    (y Group.- x) Mul.·
      powerSeriesDifferenceFactor coefficients x y n
  term-difference =
      sym
        (ℝRing.·DistR-
          (coefficients (suc n))
          (y ^ⁿ suc n)
          (x ^ⁿ suc n))
    ∙ cong (coefficients (suc n) Mul.·_)
        (powerDifferenceFactor-identity x y n)
    ∙ commuteNestedProduct
        (coefficients (suc n))
        (y Group.- x)
        (powerDifferenceFactor x y n)
