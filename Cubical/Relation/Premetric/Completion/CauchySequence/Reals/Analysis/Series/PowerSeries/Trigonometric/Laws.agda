module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric.Laws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing using (CommRing→Ring)
import Cubical.Algebra.Ring.Properties as Ring
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as ℕOrder
open import Cubical.Data.Rationals.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.AtZero public
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric


private
  module ℝRing = Ring.RingTheory (CommRing→Ring ℝCommRing)


sinℝ-zero : sinℝ zeroℝ ≡ zeroℝ
sinℝ-zero =
  locallyUniformPowerSeriesValueAtZero
    sineCoefficients sineLocallyUniform


cosℝ-zero : cosℝ zeroℝ ≡ Real.ιℚ 1
cosℝ-zero =
    locallyUniformPowerSeriesValueAtZero
      cosineCoefficients cosineLocallyUniform
  ∙ exponentialCoefficient-zero


-- Negating the argument ------------------------------------------------
--
-- `alternateCoefficients` is the coefficient action induced by x ↦ -x.
-- Keeping this as a sequence equality makes the result reusable by every
-- summation interface, rather than tying parity to sinℝ and cosℝ.

alternate-neg : ∀ n value →
  ℝRing.alternate n (Neg.- value)
    ≡ Neg.- ℝRing.alternate n value
alternate-neg zero value = refl
alternate-neg (suc zero) value = refl
alternate-neg (suc (suc n)) value = alternate-neg n value


negativePower : ∀ n x →
  (Neg.- x) ^ⁿ n ≡ ℝRing.alternate n (x ^ⁿ n)
negativePower zero x = refl
negativePower (suc n) x =
    cong ((Neg.- x) Mul.·_) (negativePower n x)
  ∙ ℝRing.-DistL· x (ℝRing.alternate n (x ^ⁿ n))
  ∙ cong Neg.-_ (mul-alternate-right x n (x ^ⁿ n))
  ∙ sym (ℝRing.alternate-suc n (x Mul.· x ^ⁿ n))


alternate-mul-left : ∀ n left right →
  ℝRing.alternate n (left Mul.· right)
    ≡ ℝRing.alternate n left Mul.· right
alternate-mul-left n left right =
    cong (ℝRing.alternate n) (mul-comm left right)
  ∙ sym (mul-alternate-right right n left)
  ∙ mul-comm right (ℝRing.alternate n left)


powerSeriesTerm-negateArgument : ∀ coefficients x n →
  powerSeriesTerms coefficients (Neg.- x) n
    ≡ powerSeriesTerms (alternateCoefficients coefficients) x n
powerSeriesTerm-negateArgument coefficients x n =
    cong (coefficients n Mul.·_) (negativePower n x)
  ∙ mul-alternate-right (coefficients n) n (x ^ⁿ n)
  ∙ alternate-mul-left n (coefficients n) (x ^ⁿ n)


powerSeriesTerms-negateArgument : ∀ coefficients x →
  powerSeriesTerms coefficients (Neg.- x)
    ≡ powerSeriesTerms (alternateCoefficients coefficients) x
powerSeriesTerms-negateArgument coefficients x =
  funExt (powerSeriesTerm-negateArgument coefficients x)


IsEvenPowerSeriesCoefficients IsOddPowerSeriesCoefficients :
  RealSequence → Type₀
IsEvenPowerSeriesCoefficients coefficients =
  alternateCoefficients coefficients ≡ coefficients
IsOddPowerSeriesCoefficients coefficients =
  alternateCoefficients coefficients ≡
    negateCoefficients coefficients


evenPowerSeriesHasSumAtNegation : ∀ coefficients →
  IsEvenPowerSeriesCoefficients coefficients →
  ∀ x value →
  HasSum (powerSeriesTerms coefficients x) value →
  HasSum (powerSeriesTerms coefficients (Neg.- x)) value
evenPowerSeriesHasSumAtNegation
    coefficients parity-path x value terms-sum =
  subst (λ terms → HasSum terms value)
    (sym
      ( powerSeriesTerms-negateArgument coefficients x
      ∙ cong (λ c → powerSeriesTerms c x) parity-path))
    terms-sum


oddPowerSeriesHasSumAtNegation : ∀ coefficients →
  IsOddPowerSeriesCoefficients coefficients →
  ∀ x value →
  HasSum (powerSeriesTerms coefficients x) value →
  HasSum
    (powerSeriesTerms coefficients (Neg.- x))
    (Neg.- value)
oddPowerSeriesHasSumAtNegation
    coefficients parity-path x value terms-sum =
  subst (λ terms → HasSum terms (Neg.- value))
    (sym
      ( powerSeriesTerms-negateArgument coefficients x
      ∙ cong (λ c → powerSeriesTerms c x) parity-path))
    (negateCoefficientsHasSum coefficients x value terms-sum)


-- The parity transforms used to define sine and cosine satisfy precisely
-- the abstract coefficient predicates above.  The proofs recurse by two,
-- matching the representation and avoiding any parity decision procedure.

alternatingEvenCoefficients-isEven : ∀ coefficients →
  IsEvenPowerSeriesCoefficients
    (alternatingEvenCoefficients coefficients)
alternatingEvenCoefficients-isEven coefficients =
  funExt (even-at coefficients)
  where
  even-at : ∀ coefficients n →
    ℝRing.alternate n
      (alternatingEvenCoefficients coefficients n)
      ≡ alternatingEvenCoefficients coefficients n
  even-at coefficients zero = refl
  even-at coefficients (suc zero) = neg-zero
  even-at coefficients (suc (suc n)) =
      alternate-neg n
        (alternatingEvenCoefficients
          (coefficients ∘ suc ∘ suc) n)
    ∙ cong Neg.-_
        (even-at (coefficients ∘ suc ∘ suc) n)


alternatingOddCoefficients-isOdd : ∀ coefficients →
  IsOddPowerSeriesCoefficients
    (alternatingOddCoefficients coefficients)
alternatingOddCoefficients-isOdd coefficients =
  funExt (odd-at coefficients)
  where
  odd-at : ∀ coefficients n →
    ℝRing.alternate n
      (alternatingOddCoefficients coefficients n)
      ≡ Neg.- alternatingOddCoefficients coefficients n
  odd-at coefficients zero = sym neg-zero
  odd-at coefficients (suc zero) = refl
  odd-at coefficients (suc (suc n)) =
      alternate-neg n
        (alternatingOddCoefficients
          (coefficients ∘ suc ∘ suc) n)
    ∙ cong Neg.-_
        (odd-at (coefficients ∘ suc ∘ suc) n)


sineCoefficients-isOdd :
  IsOddPowerSeriesCoefficients sineCoefficients
sineCoefficients-isOdd =
  alternatingOddCoefficients-isOdd exponentialCoefficients


cosineCoefficients-isEven :
  IsEvenPowerSeriesCoefficients cosineCoefficients
cosineCoefficients-isEven =
  alternatingEvenCoefficients-isEven exponentialCoefficients


sinℝ-neg : ∀ x → sinℝ (Neg.- x) ≡ Neg.- sinℝ x
sinℝ-neg x =
  seriesSumIndependent
    (powerSeriesTerms sineCoefficients (Neg.- x))
    (sinℝ (Neg.- x) , sinℝHasSum (Neg.- x))
    ( Neg.- sinℝ x
    , oddPowerSeriesHasSumAtNegation
        sineCoefficients sineCoefficients-isOdd
        x (sinℝ x) (sinℝHasSum x))


cosℝ-neg : ∀ x → cosℝ (Neg.- x) ≡ cosℝ x
cosℝ-neg x =
  seriesSumIndependent
    (powerSeriesTerms cosineCoefficients (Neg.- x))
    (cosℝ (Neg.- x) , cosℝHasSum (Neg.- x))
    ( cosℝ x
    , evenPowerSeriesHasSumAtNegation
        cosineCoefficients cosineCoefficients-isEven
        x (cosℝ x) (cosℝHasSum x))


-- Second derivatives ---------------------------------------------------
--
-- The derivative API deliberately represents the derivative as a total
-- function.  A second derivative is therefore just a composable pair of
-- checked first-derivative witnesses.

IsSecondDerivative :
  (function first-derivative second-derivative :
    Real.ℝ → Real.ℝ) → Type₀
IsSecondDerivative function first-derivative second-derivative =
  IsDerivative function first-derivative ×
  IsDerivative first-derivative second-derivative


negativeSinℝHasDerivativeNegativeCosℝ :
  IsDerivative (Neg.-_ ∘ sinℝ) (Neg.-_ ∘ cosℝ)
negativeSinℝHasDerivativeNegativeCosℝ =
  negHasDerivative sinℝ cosℝ sinℝHasDerivativeCosℝ


sinℝHasSecondDerivativeNegativeSelf :
  IsSecondDerivative sinℝ cosℝ (Neg.-_ ∘ sinℝ)
sinℝHasSecondDerivativeNegativeSelf =
  sinℝHasDerivativeCosℝ , cosℝHasDerivativeNegativeSinℝ


cosℝHasSecondDerivativeNegativeSelf :
  IsSecondDerivative
    cosℝ (Neg.-_ ∘ sinℝ) (Neg.-_ ∘ cosℝ)
cosℝHasSecondDerivativeNegativeSelf =
  cosℝHasDerivativeNegativeSinℝ ,
  negativeSinℝHasDerivativeNegativeCosℝ
