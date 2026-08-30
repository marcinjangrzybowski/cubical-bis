module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Product where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
  using (ℕ ; suc ; _∸_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.Algebra.CommRing

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (_<ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Convolution
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.ConvolutionAbsolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Comparison
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Convergence


private
  oneℝ : Real.ℝ
  oneℝ = CommRingStr.1r (snd ℝCommRing)


boundedPowerSplit : ∀ (x : Real.ℝ) (n k : ℕ) →
  k ℕ.≤ n →
  x ^ⁿ k Mul.· x ^ⁿ (n ∸ k) ≡ x ^ⁿ n
boundedPowerSplit x n k k≤n =
  ℝExponentiation.·-of-^-is-^-of-+ x k (n ∸ k)
  ∙ cong (x ^ⁿ_)
      (ℕ.+-comm k (n ∸ k)
      ∙ ℕ.≤-∸-+-cancel k≤n)


rearrangePowerSeriesTerm :
  ∀ (a b : RealSequence) (x : Real.ℝ) (n k : ℕ) →
  k ℕ.≤ n →
  (a k Mul.· b (n ∸ k)) Mul.· x ^ⁿ n ≡
  (a k Mul.· x ^ⁿ k) Mul.·
    (b (n ∸ k) Mul.· x ^ⁿ (n ∸ k))
rearrangePowerSeriesTerm a b x n k k≤n =
  cong ((a k Mul.· b (n ∸ k)) Mul.·_)
      (sym (boundedPowerSplit x n k k≤n))
  ∙ rearrange
      (a k) (b (n ∸ k))
      (x ^ⁿ k) (x ^ⁿ (n ∸ k))
  where
  rearrange : ∀ p q r s →
    (p Mul.· q) Mul.· (r Mul.· s) ≡
    (p Mul.· r) Mul.· (q Mul.· s)
  rearrange p q r s =
    sym (mul-assoc p q (r Mul.· s))
    ∙ cong (p Mul.·_) (mul-assoc q r s)
    ∙ cong (λ z → p Mul.· (z Mul.· s)) (mul-comm q r)
    ∙ cong (p Mul.·_) (sym (mul-assoc r q s))
    ∙ mul-assoc p r (q Mul.· s)


powerSeriesTerms-cauchyProduct :
  ∀ (a b : RealSequence) (x : Real.ℝ) (n : ℕ) →
  powerSeriesTerms (cauchyProduct a b) x n ≡
  cauchyProduct
    (powerSeriesTerms a x)
    (powerSeriesTerms b x) n
powerSeriesTerms-cauchyProduct a b x n =
  sym
    (partialSum-right-scale
      (λ k → a k Mul.· b (n ∸ k))
      (x ^ⁿ n) (suc n))
  ∙ partialSum-pointwiseBefore
      (λ k → (a k Mul.· b (n ∸ k)) Mul.· x ^ⁿ n)
      (λ k →
        (a k Mul.· x ^ⁿ k) Mul.·
        (b (n ∸ k) Mul.· x ^ⁿ (n ∸ k)))
      (suc n)
      (λ k k<sucn →
        rearrangePowerSeriesTerm a b x n k
          (ℕ.pred-≤-pred k<sucn))


powerSeriesTerms-cauchyProduct-sequence :
  ∀ (a b : RealSequence) (x : Real.ℝ) →
  powerSeriesTerms (cauchyProduct a b) x ≡
  cauchyProduct
    (powerSeriesTerms a x)
    (powerSeriesTerms b x)
powerSeriesTerms-cauchyProduct-sequence a b x =
  funExt (powerSeriesTerms-cauchyProduct a b x)


PowerSeriesProductRectangularApproximation :
  RealSequence → RealSequence → Real.ℝ → Type₀
PowerSeriesProductRectangularApproximation a b x =
  CauchyProductRectangularApproximation
    (powerSeriesTerms a x) (powerSeriesTerms b x)


-- The purely algebraic product layer takes exactly the analytic condition
-- it needs.  A Mertens theorem can later produce this radiuswise truncated
-- approximation from absolute convergence, without changing this API.

powerSeriesCauchyProductSummableByApproximation :
  ∀ (a b : RealSequence) (x : Real.ℝ) →
  (a-summable : PowerSeriesSummableAt a x) →
  (b-summable : PowerSeriesSummableAt b x) →
  PowerSeriesProductRectangularApproximation a b x →
  PowerSeriesSummableAt (cauchyProduct a b) x
powerSeriesCauchyProductSummableByApproximation
  a b x a-summable b-summable approximation =
  subst Summable
    (sym (powerSeriesTerms-cauchyProduct-sequence a b x))
    (cauchyProductSummable
      (powerSeriesTerms a x) (powerSeriesTerms b x)
      a-summable b-summable approximation)


powerSeriesValue-cauchyProductByApproximation :
  ∀ (a b : RealSequence) (x : Real.ℝ) →
  (a-summable : PowerSeriesSummableAt a x) →
  (b-summable : PowerSeriesSummableAt b x) →
  (product-summable :
    PowerSeriesSummableAt (cauchyProduct a b) x) →
  PowerSeriesProductRectangularApproximation a b x →
  powerSeriesValue (cauchyProduct a b) x product-summable ≡
  powerSeriesValue a x a-summable Mul.·
    powerSeriesValue b x b-summable
powerSeriesValue-cauchyProductByApproximation
  a b x a-summable b-summable
  product-summable approximation =
  seriesSumIndependent coefficient-product-terms
    product-summable target-summable
  where
  coefficient-product-terms : RealSequence
  coefficient-product-terms =
    powerSeriesTerms (cauchyProduct a b) x

  target : Real.ℝ
  target =
    powerSeriesValue a x a-summable Mul.·
      powerSeriesValue b x b-summable

  term-product-has-sum :
    HasSum
      (cauchyProduct
        (powerSeriesTerms a x) (powerSeriesTerms b x))
      target
  term-product-has-sum =
    cauchyProductHasSum
      (powerSeriesTerms a x) (powerSeriesTerms b x)
      (powerSeriesValue a x a-summable)
      (powerSeriesValue b x b-summable)
      (seriesSumHasSum (powerSeriesTerms a x) a-summable)
      (seriesSumHasSum (powerSeriesTerms b x) b-summable)
      approximation

  coefficient-product-has-sum :
    HasSum coefficient-product-terms target
  coefficient-product-has-sum =
    subst (λ terms → HasSum terms target)
      (sym (powerSeriesTerms-cauchyProduct-sequence a b x))
      term-product-has-sum

  target-summable : Summable coefficient-product-terms
  target-summable = target , coefficient-product-has-sum


-- Absolute convergence now discharges rectangular approximation through
-- the radiuswise Mertens theorem.  Unlike the older implementation, no
-- explicit bounds on the absolute sums need to be threaded through this
-- power-series API.

powerSeriesProductRectangularApproximation :
  ∀ C D (a b : RealSequence) (x : Real.ℝ) →
  CoefficientAbsBound C a → CoefficientAbsBound D b →
  RationalContractionBound x →
  PowerSeriesProductRectangularApproximation a b x
powerSeriesProductRectangularApproximation
  C D a b x a-bounded b-bounded contraction =
  absoluteMertensRectangularApproximation
    (powerSeriesTerms a x) (powerSeriesTerms b x)
    (powerSeriesIsAbsolutelyCauchy
      C a x a-bounded contraction)
    (powerSeriesIsAbsolutelyCauchy
      D b x b-bounded contraction)


powerSeriesProductRectangularApproximationOfAbs<1 :
  ∀ C D (a b : RealSequence) (x : Real.ℝ) →
  CoefficientAbsBound C a → CoefficientAbsBound D b →
  Abs.absℝ x <ℝ oneℝ →
  PowerSeriesProductRectangularApproximation a b x
powerSeriesProductRectangularApproximationOfAbs<1
  C D a b x a-bounded b-bounded absx<1 =
  absoluteMertensRectangularApproximation
    (powerSeriesTerms a x) (powerSeriesTerms b x)
    (powerSeriesIsAbsolutelyCauchyOfAbs<1
      C a x a-bounded absx<1)
    (powerSeriesIsAbsolutelyCauchyOfAbs<1
      D b x b-bounded absx<1)


powerSeriesCauchyProductSummable :
  ∀ C D (a b : RealSequence) (x : Real.ℝ) →
  CoefficientAbsBound C a → CoefficientAbsBound D b →
  RationalContractionBound x →
  PowerSeriesSummableAt (cauchyProduct a b) x
powerSeriesCauchyProductSummable
  C D a b x a-bounded b-bounded contraction =
  powerSeriesCauchyProductSummableByApproximation
    a b x
    (powerSeriesIsSummable C a x a-bounded contraction)
    (powerSeriesIsSummable D b x b-bounded contraction)
    (powerSeriesProductRectangularApproximation
      C D a b x a-bounded b-bounded contraction)


powerSeriesCauchyProductSummableOfAbs<1 :
  ∀ C D (a b : RealSequence) (x : Real.ℝ) →
  CoefficientAbsBound C a → CoefficientAbsBound D b →
  Abs.absℝ x <ℝ oneℝ →
  PowerSeriesSummableAt (cauchyProduct a b) x
powerSeriesCauchyProductSummableOfAbs<1
  C D a b x a-bounded b-bounded absx<1 =
  powerSeriesCauchyProductSummableByApproximation
    a b x
    (powerSeriesIsSummableOfAbs<1 C a x a-bounded absx<1)
    (powerSeriesIsSummableOfAbs<1 D b x b-bounded absx<1)
    (powerSeriesProductRectangularApproximationOfAbs<1
      C D a b x a-bounded b-bounded absx<1)


powerSeriesValue-cauchyProduct :
  ∀ C D (a b : RealSequence) (x : Real.ℝ) →
  CoefficientAbsBound C a → CoefficientAbsBound D b →
  RationalContractionBound x →
  (a-summable : PowerSeriesSummableAt a x) →
  (b-summable : PowerSeriesSummableAt b x) →
  (product-summable :
    PowerSeriesSummableAt (cauchyProduct a b) x) →
  powerSeriesValue (cauchyProduct a b) x product-summable ≡
  powerSeriesValue a x a-summable Mul.·
    powerSeriesValue b x b-summable
powerSeriesValue-cauchyProduct
  C D a b x a-bounded b-bounded contraction
  a-summable b-summable product-summable =
  powerSeriesValue-cauchyProductByApproximation
    a b x a-summable b-summable product-summable
    (powerSeriesProductRectangularApproximation
      C D a b x a-bounded b-bounded contraction)


powerSeriesValue-cauchyProductOfAbs<1 :
  ∀ C D (a b : RealSequence) (x : Real.ℝ) →
  CoefficientAbsBound C a → CoefficientAbsBound D b →
  Abs.absℝ x <ℝ oneℝ →
  (a-summable : PowerSeriesSummableAt a x) →
  (b-summable : PowerSeriesSummableAt b x) →
  (product-summable :
    PowerSeriesSummableAt (cauchyProduct a b) x) →
  powerSeriesValue (cauchyProduct a b) x product-summable ≡
  powerSeriesValue a x a-summable Mul.·
    powerSeriesValue b x b-summable
powerSeriesValue-cauchyProductOfAbs<1
  C D a b x a-bounded b-bounded absx<1
  a-summable b-summable product-summable =
  powerSeriesValue-cauchyProductByApproximation
    a b x a-summable b-summable product-summable
    (powerSeriesProductRectangularApproximationOfAbs<1
      C D a b x a-bounded b-bounded absx<1)
