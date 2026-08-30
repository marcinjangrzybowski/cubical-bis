module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LinearGrowth where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ
  using (ℕ ; zero ; suc ; _∸_)
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Base using (fromNatℚ)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Convolution
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.ConvolutionAbsolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Geometric.Comparison
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Geometric
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Product
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Convergence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Majorant
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative


private
  oneℝ : Real.ℝ
  oneℝ = CommRingStr.1r (snd ℝCommRing)

  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing


linearGrowthCoefficients : RealSequence
linearGrowthCoefficients n = realNatural (suc n)


linearGrowthCoefficients-nonnegative :
  NonnegativeCoefficients linearGrowthCoefficients
linearGrowthCoefficients-nonnegative n =
  realNatural-nonnegative (suc n)


partialSum-unitCoefficients : ∀ n →
  partialSum unitCoefficients n ≡ realNatural n
partialSum-unitCoefficients zero =
  sym realNatural-zero
partialSum-unitCoefficients (suc n) =
  cong (Add._+ oneℝ) (partialSum-unitCoefficients n)
  ∙ cong (realNatural n Add.+_) (sym realNatural-one)
  ∙ sym (realNatural-suc n)


cauchyProduct-unitCoefficients-left : ∀ coefficients n →
  cauchyProduct unitCoefficients coefficients n ≡
  partialSum coefficients (suc n)
cauchyProduct-unitCoefficients-left coefficients n =
  cauchyProduct-comm unitCoefficients coefficients n
  ∙ partialSum-pointwise
      (λ k → coefficients k Mul.· unitCoefficients (n ∸ k))
      coefficients
      (λ k → mul-one-right (coefficients k))
      (suc n)


cauchyProduct-unitCoefficients : ∀ n →
  cauchyProduct unitCoefficients unitCoefficients n ≡
  linearGrowthCoefficients n
cauchyProduct-unitCoefficients n =
  cauchyProduct-unitCoefficients-left unitCoefficients n
  ∙ partialSum-unitCoefficients (suc n)


cauchyProduct-unitCoefficients-sequence :
  cauchyProduct unitCoefficients unitCoefficients ≡
  linearGrowthCoefficients
cauchyProduct-unitCoefficients-sequence =
  funExt cauchyProduct-unitCoefficients


powerSeriesTerms-linearGrowth : ∀ x →
  powerSeriesTerms linearGrowthCoefficients x ≡
  cauchyProduct (geometricTerms x) (geometricTerms x)
powerSeriesTerms-linearGrowth x =
  cong (λ coefficients → powerSeriesTerms coefficients x)
    (sym cauchyProduct-unitCoefficients-sequence)
  ∙ powerSeriesTerms-cauchyProduct-sequence
      unitCoefficients unitCoefficients x
  ∙ cong₂ cauchyProduct
      (powerSeriesTerms-unitCoefficients-sequence x)
      (powerSeriesTerms-unitCoefficients-sequence x)


linearGrowthPowerSeriesIsAbsolutelyCauchyOfAbs<1 : ∀ x →
  Abs.absℝ x <ℝ oneℝ →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms linearGrowthCoefficients x)
linearGrowthPowerSeriesIsAbsolutelyCauchyOfAbs<1 x absx<1 =
  subst IsAbsolutelyCauchySeries
    (sym (powerSeriesTerms-linearGrowth x))
    (absoluteMertensCauchyProductIsAbsolutelyCauchy
      (geometricTerms x) (geometricTerms x)
      (geometricSeriesIsAbsolutelyCauchyOfAbs<1 x absx<1)
      (geometricSeriesIsAbsolutelyCauchyOfAbs<1 x absx<1))


formalDerivativeConstantMajorantPath : ∀ C →
  formalDerivativeMajorant (constantCoefficientMajorant C) ≡
  scaleSeries (Real.ιℚ (fst C)) linearGrowthCoefficients
formalDerivativeConstantMajorantPath C =
  funExt λ n →
    mul-comm (realNatural (suc n)) (Real.ιℚ (fst C))


formalDerivativeConstantMajorantIsAbsolutelyCauchyOfAbs<1 : ∀ C x →
  Abs.absℝ x <ℝ oneℝ →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant (constantCoefficientMajorant C)) x)
formalDerivativeConstantMajorantIsAbsolutelyCauchyOfAbs<1 C x absx<1 =
  subst IsAbsolutelyCauchySeries (sym derivativeTermsPath)
    (scaleSeriesIsAbsolutelyCauchy
      (Real.ιℚ (fst C))
      (powerSeriesTerms linearGrowthCoefficients x)
      (linearGrowthPowerSeriesIsAbsolutelyCauchyOfAbs<1 x absx<1))
  where
  derivativeTermsPath :
    powerSeriesTerms
        (formalDerivativeMajorant (constantCoefficientMajorant C)) x
      ≡
    scaleSeries (Real.ιℚ (fst C))
      (powerSeriesTerms linearGrowthCoefficients x)
  derivativeTermsPath =
    cong (λ coefficients → powerSeriesTerms coefficients x)
      (formalDerivativeConstantMajorantPath C)
    ∙ powerSeriesTerms-scale-sequence
        (Real.ιℚ (fst C)) linearGrowthCoefficients x


formalDerivativeConstantMajorantIsCauchyOfAbs<1 : ∀ C x →
  Abs.absℝ x <ℝ oneℝ →
  IsCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant (constantCoefficientMajorant C)) x)
formalDerivativeConstantMajorantIsCauchyOfAbs<1 C x absx<1 =
  absoluteCauchySeriesIsCauchy _
    (formalDerivativeConstantMajorantIsAbsolutelyCauchyOfAbs<1
      C x absx<1)


positiveRationalRadiusAbs<1 : ∀ q →
  fst q ℚ.< 1 →
  Abs.absℝ (Real.ιℚ (fst q)) <ℝ oneℝ
positiveRationalRadiusAbs<1 q q<1 =
  subst (_<ℝ oneℝ) (sym absPath)
    (<ℚ→<ℝ (fst q) 1 q<1)
  where
  absPath :
    Abs.absℝ (Real.ιℚ (fst q)) ≡ Real.ιℚ (fst q)
  absPath =
    Abs.absℝ-ι (fst q)
    ∙ cong Real.ιℚ
        (ℚOrder.0≤→abs≡id (fst q)
          (ℚ.<Weaken≤ 0 (fst q) (snd q)))


formalDerivativeConstantMajorantIsCauchyAtPositiveRational : ∀ C q →
  fst q ℚ.< 1 →
  IsCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant (constantCoefficientMajorant C))
      (Real.ιℚ (fst q)))
formalDerivativeConstantMajorantIsCauchyAtPositiveRational C q q<1 =
  formalDerivativeConstantMajorantIsCauchyOfAbs<1
    C (Real.ιℚ (fst q))
    (positiveRationalRadiusAbs<1 q q<1)
