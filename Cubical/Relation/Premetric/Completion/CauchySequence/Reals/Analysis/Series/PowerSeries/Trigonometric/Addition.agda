module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Tactics.CommRingSolver

open import Cubical.Data.Nat as ℕ
  using (ℕ ; zero ; suc ; _∸_)
  renaming (_+_ to _+ℕ_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base
open import Cubical.Data.FinData
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.BinomialThm
import Cubical.Algebra.Ring.Properties as Ring
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Convolution
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.ConvolutionAbsolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric


private
  module ℝBinomial = BinomialThm ℝCommRing
  module ℝRing = Ring.RingTheory (CommRing→Ring ℝCommRing)

  module SignAlgebra {ℓ} (R : CommRing ℓ) where
    open CommRingStr (snd R)
    open Ring.RingTheory (CommRing→Ring R)

    sine-base : ∀ sine-right cosine-right →
      0r · cosine-right + 1r · sine-right ≡ sine-right
    sine-base sine-right cosine-right = solve! R

    cosine-base : ∀ sine-right cosine-right →
      1r · cosine-right + (- (0r · sine-right)) ≡ cosine-right
    cosine-base sine-right cosine-right = solve! R

    sine-step : ∀ sine-left cosine-left sine-right cosine-right →
      cosine-left · cosine-right + (- sine-left) · sine-right
        ≡ cosine-left · cosine-right +
            (- (sine-left · sine-right))
    sine-step sine-left cosine-left sine-right cosine-right = solve! R

    cosine-step : ∀ sine-left cosine-left sine-right cosine-right →
      (- sine-left) · cosine-right +
          (- (cosine-left · sine-right))
        ≡
      (- (sine-left · cosine-right +
        cosine-left · sine-right))
    cosine-step sine-left cosine-left sine-right cosine-right = solve! R

    combine-sine-products :
      ∀ sine-left cosine-left sine-right cosine-right
        left-coefficient left-power right-coefficient right-power →
      (((sine-left · left-coefficient) · left-power) ·
          ((cosine-right · right-coefficient) · right-power)) +
        (((cosine-left · left-coefficient) · left-power) ·
          ((sine-right · right-coefficient) · right-power))
        ≡
      (sine-left · cosine-right + cosine-left · sine-right) ·
        ((left-coefficient · left-power) ·
          (right-coefficient · right-power))
    combine-sine-products
      sine-left cosine-left sine-right cosine-right
      left-coefficient left-power right-coefficient right-power =
      solve! R

    combine-cosine-products :
      ∀ sine-left cosine-left sine-right cosine-right
        left-coefficient left-power right-coefficient right-power →
      (((cosine-left · left-coefficient) · left-power) ·
          ((cosine-right · right-coefficient) · right-power)) +
        (- (((sine-left · left-coefficient) · left-power) ·
          ((sine-right · right-coefficient) · right-power)))
        ≡
      (cosine-left · cosine-right +
          (- (sine-left · sine-right))) ·
        ((left-coefficient · left-power) ·
          (right-coefficient · right-power))
    combine-cosine-products
      sine-left cosine-left sine-right cosine-right
      left-coefficient left-power right-coefficient right-power =
      solve! R


-- The two four-periodic scalar sequences carry all trigonometric signs.
-- Separating them from the reciprocal-factorial magnitudes keeps the
-- addition algebra independent of the analytic construction of exp.

mutual
  sineSign cosineSign : ℕ → Real.ℝ
  sineSign zero = zeroℝ
  sineSign (suc n) = cosineSign n
  cosineSign zero = Real.ιℚ 1
  cosineSign (suc n) = Neg.- sineSign n


alternatingOddCoefficients-as-sign :
  ∀ (coefficients : RealSequence) (n : ℕ) →
  alternatingOddCoefficients coefficients n
    ≡ sineSign n Mul.· coefficients n
alternatingOddCoefficients-as-sign coefficients zero =
  sym (mul-zero-left (coefficients zero))
alternatingOddCoefficients-as-sign coefficients (suc zero) =
  sym (mul-one-left (coefficients (suc zero)))
alternatingOddCoefficients-as-sign coefficients (suc (suc n)) =
    cong Neg.-_
      (alternatingOddCoefficients-as-sign
        (λ k → coefficients (suc (suc k))) n)
  ∙ sym
      (ℝRing.-DistL·
        (sineSign n) (coefficients (suc (suc n))))


alternatingEvenCoefficients-as-sign :
  ∀ (coefficients : RealSequence) (n : ℕ) →
  alternatingEvenCoefficients coefficients n
    ≡ cosineSign n Mul.· coefficients n
alternatingEvenCoefficients-as-sign coefficients zero =
  sym (mul-one-left (coefficients zero))
alternatingEvenCoefficients-as-sign coefficients (suc zero) =
    sym (mul-zero-left (coefficients (suc zero)))
  ∙ cong (Mul._· coefficients (suc zero)) (sym neg-zero)
alternatingEvenCoefficients-as-sign coefficients (suc (suc n)) =
    cong Neg.-_
      (alternatingEvenCoefficients-as-sign
        (λ k → coefficients (suc (suc k))) n)
  ∙ sym
      (ℝRing.-DistL·
        (cosineSign n) (coefficients (suc (suc n))))


sineCoefficient-as-sign : ∀ n →
  sineCoefficients n
    ≡ sineSign n Mul.· exponentialCoefficients n
sineCoefficient-as-sign =
  alternatingOddCoefficients-as-sign exponentialCoefficients


cosineCoefficient-as-sign : ∀ n →
  cosineCoefficients n
    ≡ cosineSign n Mul.· exponentialCoefficients n
cosineCoefficient-as-sign =
  alternatingEvenCoefficients-as-sign exponentialCoefficients


-- These are the finite algebraic heart of both addition formulas.
-- Recursing on the left degree proves both identities simultaneously;
-- the successor equations exchange sine and cosine exactly once.

trigonometricSign-addition : ∀ left right →
  ( sineSign left Mul.· cosineSign right Add.+
      cosineSign left Mul.· sineSign right
      ≡ sineSign (left +ℕ right))
  ×
  ( cosineSign left Mul.· cosineSign right Add.+
      Neg.- (sineSign left Mul.· sineSign right)
      ≡ cosineSign (left +ℕ right))
trigonometricSign-addition zero right =
  ( SignAlgebra.sine-base ℝCommRing
      (sineSign right) (cosineSign right)
  , SignAlgebra.cosine-base ℝCommRing
      (sineSign right) (cosineSign right))
trigonometricSign-addition (suc left) right =
  ( sine-step ∙ snd induction
  , cosine-step ∙ cong Neg.-_ (fst induction))
  where
  induction = trigonometricSign-addition left right

  sine-step :
    cosineSign left Mul.· cosineSign right Add.+
      (Neg.- sineSign left) Mul.· sineSign right
      ≡
    cosineSign left Mul.· cosineSign right Add.+
      Neg.- (sineSign left Mul.· sineSign right)
  sine-step =
    SignAlgebra.sine-step ℝCommRing
      (sineSign left) (cosineSign left)
      (sineSign right) (cosineSign right)

  cosine-step :
    (Neg.- sineSign left) Mul.· cosineSign right Add.+
      Neg.- (cosineSign left Mul.· sineSign right)
      ≡
    Neg.-
      (sineSign left Mul.· cosineSign right Add.+
        cosineSign left Mul.· sineSign right)
  cosine-step =
    SignAlgebra.cosine-step ℝCommRing
      (sineSign left) (cosineSign left)
      (sineSign right) (cosineSign right)


-- Bivariate summand identities ----------------------------------------
--
-- The exponential coefficient product supplies the binomial magnitude;
-- the sign theorem supplies its sine or cosine mask.  These lemmas are the
-- reusable finite identities consumed by the convolution proofs below.

sineAdditionProductSummand : ∀ x y n k →
  (k≤n : k ℕ.≤ n) →
  ( powerSeriesTerms sineCoefficients x k Mul.·
      powerSeriesTerms cosineCoefficients y (n ∸ k)) Add.+
    ( powerSeriesTerms cosineCoefficients x k Mul.·
      powerSeriesTerms sineCoefficients y (n ∸ k))
    ≡
  sineCoefficients n Mul.·
    ((ℝBinomial._choose_ n k Mul.· x ^ⁿ k) Mul.·
      y ^ⁿ (n ∸ k))
sineAdditionProductSummand x y n k k≤n =
    expand-coefficients
  ∙ SignAlgebra.combine-sine-products ℝCommRing
      (sineSign k) (cosineSign k)
      (sineSign remainder) (cosineSign remainder)
      (exponentialCoefficients k) (x ^ⁿ k)
      (exponentialCoefficients remainder) (y ^ⁿ remainder)
  ∙ cong (Mul._· (left-term Mul.· right-term))
      (fst (trigonometricSign-addition k remainder))
  ∙ cong
      (λ index →
        sineSign index Mul.· (left-term Mul.· right-term))
      total-index
  ∙ cong (sineSign n Mul.·_)
      (exponentialProductSummand-binomial x y n k k≤n)
  ∙ mul-assoc
      (sineSign n) (exponentialCoefficients n) binomial-term
  ∙ cong (Mul._· binomial-term)
      (sym (sineCoefficient-as-sign n))
  where
  remainder : ℕ
  remainder = n ∸ k

  left-term right-term binomial-term : Real.ℝ
  left-term =
    exponentialCoefficients k Mul.· x ^ⁿ k
  right-term =
    exponentialCoefficients remainder Mul.· y ^ⁿ remainder
  binomial-term =
    (ℝBinomial._choose_ n k Mul.· x ^ⁿ k) Mul.·
      y ^ⁿ remainder

  total-index : k +ℕ remainder ≡ n
  total-index =
    ℕ.+-comm k remainder ∙ ℕ.[n-m]+m k n k≤n

  expand-coefficients :
    ( powerSeriesTerms sineCoefficients x k Mul.·
        powerSeriesTerms cosineCoefficients y remainder) Add.+
      ( powerSeriesTerms cosineCoefficients x k Mul.·
        powerSeriesTerms sineCoefficients y remainder)
      ≡
    (((sineSign k Mul.· exponentialCoefficients k) Mul.·
        x ^ⁿ k) Mul.·
      ((cosineSign remainder Mul.·
          exponentialCoefficients remainder) Mul.·
        y ^ⁿ remainder)) Add.+
    (((cosineSign k Mul.· exponentialCoefficients k) Mul.·
        x ^ⁿ k) Mul.·
      ((sineSign remainder Mul.·
          exponentialCoefficients remainder) Mul.·
        y ^ⁿ remainder))
  expand-coefficients =
    cong₂ Add._+_
      (cong₂ Mul._·_
        (cong (Mul._· x ^ⁿ k) (sineCoefficient-as-sign k))
        (cong (Mul._· y ^ⁿ remainder)
          (cosineCoefficient-as-sign remainder)))
      (cong₂ Mul._·_
        (cong (Mul._· x ^ⁿ k) (cosineCoefficient-as-sign k))
        (cong (Mul._· y ^ⁿ remainder)
          (sineCoefficient-as-sign remainder)))


cosineAdditionProductSummand : ∀ x y n k →
  (k≤n : k ℕ.≤ n) →
  ( powerSeriesTerms cosineCoefficients x k Mul.·
      powerSeriesTerms cosineCoefficients y (n ∸ k)) Group.-
    ( powerSeriesTerms sineCoefficients x k Mul.·
      powerSeriesTerms sineCoefficients y (n ∸ k))
    ≡
  cosineCoefficients n Mul.·
    ((ℝBinomial._choose_ n k Mul.· x ^ⁿ k) Mul.·
      y ^ⁿ (n ∸ k))
cosineAdditionProductSummand x y n k k≤n =
    expand-coefficients
  ∙ SignAlgebra.combine-cosine-products ℝCommRing
      (sineSign k) (cosineSign k)
      (sineSign remainder) (cosineSign remainder)
      (exponentialCoefficients k) (x ^ⁿ k)
      (exponentialCoefficients remainder) (y ^ⁿ remainder)
  ∙ cong (Mul._· (left-term Mul.· right-term))
      (snd (trigonometricSign-addition k remainder))
  ∙ cong
      (λ index →
        cosineSign index Mul.· (left-term Mul.· right-term))
      total-index
  ∙ cong (cosineSign n Mul.·_)
      (exponentialProductSummand-binomial x y n k k≤n)
  ∙ mul-assoc
      (cosineSign n) (exponentialCoefficients n) binomial-term
  ∙ cong (Mul._· binomial-term)
      (sym (cosineCoefficient-as-sign n))
  where
  remainder : ℕ
  remainder = n ∸ k

  left-term right-term binomial-term : Real.ℝ
  left-term =
    exponentialCoefficients k Mul.· x ^ⁿ k
  right-term =
    exponentialCoefficients remainder Mul.· y ^ⁿ remainder
  binomial-term =
    (ℝBinomial._choose_ n k Mul.· x ^ⁿ k) Mul.·
      y ^ⁿ remainder

  total-index : k +ℕ remainder ≡ n
  total-index =
    ℕ.+-comm k remainder ∙ ℕ.[n-m]+m k n k≤n

  expand-coefficients :
    ( powerSeriesTerms cosineCoefficients x k Mul.·
        powerSeriesTerms cosineCoefficients y remainder) Group.-
      ( powerSeriesTerms sineCoefficients x k Mul.·
        powerSeriesTerms sineCoefficients y remainder)
      ≡
    (((cosineSign k Mul.· exponentialCoefficients k) Mul.·
        x ^ⁿ k) Mul.·
      ((cosineSign remainder Mul.·
          exponentialCoefficients remainder) Mul.·
        y ^ⁿ remainder)) Group.-
    (((sineSign k Mul.· exponentialCoefficients k) Mul.·
        x ^ⁿ k) Mul.·
      ((sineSign remainder Mul.·
          exponentialCoefficients remainder) Mul.·
        y ^ⁿ remainder))
  expand-coefficients =
    cong₂ Group._-_
      (cong₂ Mul._·_
        (cong (Mul._· x ^ⁿ k) (cosineCoefficient-as-sign k))
        (cong (Mul._· y ^ⁿ remainder)
          (cosineCoefficient-as-sign remainder)))
      (cong₂ Mul._·_
        (cong (Mul._· x ^ⁿ k) (sineCoefficient-as-sign k))
        (cong (Mul._· y ^ⁿ remainder)
          (sineCoefficient-as-sign remainder)))


-- Finite convolution identities ---------------------------------------
--
-- These are the exact bivariate power-series identities.  They are purely
-- finite: Mertens and completeness enter only after this section.

sineAdditionConvolutionTerms : ∀ x y → RealSequence
sineAdditionConvolutionTerms x y n =
  cauchyProduct
      (powerSeriesTerms sineCoefficients x)
      (powerSeriesTerms cosineCoefficients y) n
    Add.+
  cauchyProduct
      (powerSeriesTerms cosineCoefficients x)
      (powerSeriesTerms sineCoefficients y) n


cosineAdditionConvolutionTerms : ∀ x y → RealSequence
cosineAdditionConvolutionTerms x y n =
  cauchyProduct
      (powerSeriesTerms cosineCoefficients x)
      (powerSeriesTerms cosineCoefficients y) n
    Group.-
  cauchyProduct
      (powerSeriesTerms sineCoefficients x)
      (powerSeriesTerms sineCoefficients y) n


sineAdditionConvolutionTerm : ∀ x y n →
  sineAdditionConvolutionTerms x y n
    ≡ powerSeriesTerms sineCoefficients (x Add.+ y) n
sineAdditionConvolutionTerm x y n =
    sym
      (partialSum-add
        (λ k →
          powerSeriesTerms sineCoefficients x k Mul.·
            powerSeriesTerms cosineCoefficients y (n ∸ k))
        (λ k →
          powerSeriesTerms cosineCoefficients x k Mul.·
            powerSeriesTerms sineCoefficients y (n ∸ k))
        (suc n))
  ∙ partialSum-pointwiseBefore
      (λ k →
        (powerSeriesTerms sineCoefficients x k Mul.·
          powerSeriesTerms cosineCoefficients y (n ∸ k)) Add.+
        (powerSeriesTerms cosineCoefficients x k Mul.·
          powerSeriesTerms sineCoefficients y (n ∸ k)))
      (scaleSeries (sineCoefficients n) binomial-terms)
      (suc n)
      (λ k k<sucn →
        sineAdditionProductSummand x y n k
          (ℕ.pred-≤-pred k<sucn))
  ∙ partialSum-scale
      (sineCoefficients n) binomial-terms (suc n)
  ∙ cong (sineCoefficients n Mul.·_)
      (partialSum-as-finSum binomial-terms (suc n))
  ∙ cong (sineCoefficients n Mul.·_)
      (sym (ℝBinomial.BinomialThm n x y))
  where
  binomial-terms : RealSequence
  binomial-terms k =
    (ℝBinomial._choose_ n k Mul.· x ^ⁿ k) Mul.·
      y ^ⁿ (n ∸ k)


cosineAdditionConvolutionTerm : ∀ x y n →
  cosineAdditionConvolutionTerms x y n
    ≡ powerSeriesTerms cosineCoefficients (x Add.+ y) n
cosineAdditionConvolutionTerm x y n =
    sym
      (partialSum-sub
        (λ k →
          powerSeriesTerms cosineCoefficients x k Mul.·
            powerSeriesTerms cosineCoefficients y (n ∸ k))
        (λ k →
          powerSeriesTerms sineCoefficients x k Mul.·
            powerSeriesTerms sineCoefficients y (n ∸ k))
        (suc n))
  ∙ partialSum-pointwiseBefore
      (λ k →
        (powerSeriesTerms cosineCoefficients x k Mul.·
          powerSeriesTerms cosineCoefficients y (n ∸ k)) Group.-
        (powerSeriesTerms sineCoefficients x k Mul.·
          powerSeriesTerms sineCoefficients y (n ∸ k)))
      (scaleSeries (cosineCoefficients n) binomial-terms)
      (suc n)
      (λ k k<sucn →
        cosineAdditionProductSummand x y n k
          (ℕ.pred-≤-pred k<sucn))
  ∙ partialSum-scale
      (cosineCoefficients n) binomial-terms (suc n)
  ∙ cong (cosineCoefficients n Mul.·_)
      (partialSum-as-finSum binomial-terms (suc n))
  ∙ cong (cosineCoefficients n Mul.·_)
      (sym (ℝBinomial.BinomialThm n x y))
  where
  binomial-terms : RealSequence
  binomial-terms k =
    (ℝBinomial._choose_ n k Mul.· x ^ⁿ k) Mul.·
      y ^ⁿ (n ∸ k)


sineAdditionConvolutionTerms-sequence : ∀ x y →
  sineAdditionConvolutionTerms x y
    ≡ powerSeriesTerms sineCoefficients (x Add.+ y)
sineAdditionConvolutionTerms-sequence x y =
  funExt (sineAdditionConvolutionTerm x y)


cosineAdditionConvolutionTerms-sequence : ∀ x y →
  cosineAdditionConvolutionTerms x y
    ≡ powerSeriesTerms cosineCoefficients (x Add.+ y)
cosineAdditionConvolutionTerms-sequence x y =
  funExt (cosineAdditionConvolutionTerm x y)


-- Mertens bridges ------------------------------------------------------
--
-- Absolute Cauchyness is sufficient and proposition-valued.  The chosen
-- bounds internal to Mertens do not occur in this reusable sum theorem.

absoluteMertensCauchyProductHasSumFrom : ∀ a b a-value b-value →
  HasSum a a-value →
  HasSum b b-value →
  IsAbsolutelyCauchySeries a →
  IsAbsolutelyCauchySeries b →
  HasSum (cauchyProduct a b) (a-value Mul.· b-value)
absoluteMertensCauchyProductHasSumFrom
    a b a-value b-value a-sum b-sum a-absolute b-absolute =
  cauchyProductHasSum a b a-value b-value
    a-sum b-sum
    (absoluteMertensRectangularApproximation-sealed
      a b a-absolute b-absolute)


sineCosineTermsCauchyProductHasSum : ∀ x y →
  HasSum
    (cauchyProduct
      (powerSeriesTerms sineCoefficients x)
      (powerSeriesTerms cosineCoefficients y))
    (sinℝ x Mul.· cosℝ y)
sineCosineTermsCauchyProductHasSum x y =
  absoluteMertensCauchyProductHasSumFrom
    (powerSeriesTerms sineCoefficients x)
    (powerSeriesTerms cosineCoefficients y)
    (sinℝ x) (cosℝ y)
    (sinℝHasSum x) (cosℝHasSum y)
    (sinePowerSeriesIsAbsolutelyCauchy x)
    (cosinePowerSeriesIsAbsolutelyCauchy y)


cosineSineTermsCauchyProductHasSum : ∀ x y →
  HasSum
    (cauchyProduct
      (powerSeriesTerms cosineCoefficients x)
      (powerSeriesTerms sineCoefficients y))
    (cosℝ x Mul.· sinℝ y)
cosineSineTermsCauchyProductHasSum x y =
  absoluteMertensCauchyProductHasSumFrom
    (powerSeriesTerms cosineCoefficients x)
    (powerSeriesTerms sineCoefficients y)
    (cosℝ x) (sinℝ y)
    (cosℝHasSum x) (sinℝHasSum y)
    (cosinePowerSeriesIsAbsolutelyCauchy x)
    (sinePowerSeriesIsAbsolutelyCauchy y)


cosineCosineTermsCauchyProductHasSum : ∀ x y →
  HasSum
    (cauchyProduct
      (powerSeriesTerms cosineCoefficients x)
      (powerSeriesTerms cosineCoefficients y))
    (cosℝ x Mul.· cosℝ y)
cosineCosineTermsCauchyProductHasSum x y =
  absoluteMertensCauchyProductHasSumFrom
    (powerSeriesTerms cosineCoefficients x)
    (powerSeriesTerms cosineCoefficients y)
    (cosℝ x) (cosℝ y)
    (cosℝHasSum x) (cosℝHasSum y)
    (cosinePowerSeriesIsAbsolutelyCauchy x)
    (cosinePowerSeriesIsAbsolutelyCauchy y)


sineSineTermsCauchyProductHasSum : ∀ x y →
  HasSum
    (cauchyProduct
      (powerSeriesTerms sineCoefficients x)
      (powerSeriesTerms sineCoefficients y))
    (sinℝ x Mul.· sinℝ y)
sineSineTermsCauchyProductHasSum x y =
  absoluteMertensCauchyProductHasSumFrom
    (powerSeriesTerms sineCoefficients x)
    (powerSeriesTerms sineCoefficients y)
    (sinℝ x) (sinℝ y)
    (sinℝHasSum x) (sinℝHasSum y)
    (sinePowerSeriesIsAbsolutelyCauchy x)
    (sinePowerSeriesIsAbsolutelyCauchy y)


sineAdditionConvolutionHasSum : ∀ x y →
  HasSum
    (sineAdditionConvolutionTerms x y)
    ((sinℝ x Mul.· cosℝ y) Add.+
      (cosℝ x Mul.· sinℝ y))
sineAdditionConvolutionHasSum x y =
  snd
    (addSummable
      (cauchyProduct
        (powerSeriesTerms sineCoefficients x)
        (powerSeriesTerms cosineCoefficients y))
      (cauchyProduct
        (powerSeriesTerms cosineCoefficients x)
        (powerSeriesTerms sineCoefficients y))
      ( sinℝ x Mul.· cosℝ y
      , sineCosineTermsCauchyProductHasSum x y)
      ( cosℝ x Mul.· sinℝ y
      , cosineSineTermsCauchyProductHasSum x y))


cosineAdditionConvolutionHasSum : ∀ x y →
  HasSum
    (cosineAdditionConvolutionTerms x y)
    ((cosℝ x Mul.· cosℝ y) Group.-
      (sinℝ x Mul.· sinℝ y))
cosineAdditionConvolutionHasSum x y =
  snd
    (subSummable
      (cauchyProduct
        (powerSeriesTerms cosineCoefficients x)
        (powerSeriesTerms cosineCoefficients y))
      (cauchyProduct
        (powerSeriesTerms sineCoefficients x)
        (powerSeriesTerms sineCoefficients y))
      ( cosℝ x Mul.· cosℝ y
      , cosineCosineTermsCauchyProductHasSum x y)
      ( sinℝ x Mul.· sinℝ y
      , sineSineTermsCauchyProductHasSum x y))


sineAddHasAdditionSum : ∀ x y →
  HasSum
    (powerSeriesTerms sineCoefficients (x Add.+ y))
    ((sinℝ x Mul.· cosℝ y) Add.+
      (cosℝ x Mul.· sinℝ y))
sineAddHasAdditionSum x y =
  subst
    (λ terms →
      HasSum terms
        ((sinℝ x Mul.· cosℝ y) Add.+
          (cosℝ x Mul.· sinℝ y)))
    (sineAdditionConvolutionTerms-sequence x y)
    (sineAdditionConvolutionHasSum x y)


cosineAddHasAdditionSum : ∀ x y →
  HasSum
    (powerSeriesTerms cosineCoefficients (x Add.+ y))
    ((cosℝ x Mul.· cosℝ y) Group.-
      (sinℝ x Mul.· sinℝ y))
cosineAddHasAdditionSum x y =
  subst
    (λ terms →
      HasSum terms
        ((cosℝ x Mul.· cosℝ y) Group.-
          (sinℝ x Mul.· sinℝ y)))
    (cosineAdditionConvolutionTerms-sequence x y)
    (cosineAdditionConvolutionHasSum x y)


-- Total addition formulas ---------------------------------------------

sinℝ-add : ∀ x y →
  sinℝ (x Add.+ y)
    ≡ (sinℝ x Mul.· cosℝ y) Add.+
        (cosℝ x Mul.· sinℝ y)
sinℝ-add x y =
  seriesSumIndependent
    (powerSeriesTerms sineCoefficients (x Add.+ y))
    (sinℝ (x Add.+ y) , sinℝHasSum (x Add.+ y))
    ( (sinℝ x Mul.· cosℝ y) Add.+
        (cosℝ x Mul.· sinℝ y)
    , sineAddHasAdditionSum x y)


cosℝ-add : ∀ x y →
  cosℝ (x Add.+ y)
    ≡ (cosℝ x Mul.· cosℝ y) Group.-
        (sinℝ x Mul.· sinℝ y)
cosℝ-add x y =
  seriesSumIndependent
    (powerSeriesTerms cosineCoefficients (x Add.+ y))
    (cosℝ (x Add.+ y) , cosℝHasSum (x Add.+ y))
    ( (cosℝ x Mul.· cosℝ y) Group.-
        (sinℝ x Mul.· sinℝ y)
    , cosineAddHasAdditionSum x y)
