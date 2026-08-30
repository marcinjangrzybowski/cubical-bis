module Cubical.Analysis.Real.Series.PowerSeries.Exponential.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv using (invEq)

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
import Cubical.Data.Rationals.Inverse as ℚInv
open ℚInv using (_⁻¹₊)

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Geometric.Rational
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.FactorialBound
open import Cubical.Analysis.Real.Series.PowerSeries.Growth
open import Cubical.Analysis.Real.Series.PowerSeries.GrowthUniform
open import Cubical.Analysis.Real.Series.PowerSeries.Uniform


-- A global coefficient estimate 1/n! ≤ 2·(1/2)^n gives a simple
-- quantitative convergence radius of two.  The sharper entire-series tail
-- estimate can later replace this constant without changing the wrappers.
exponentialHalfGrowth : ℚ₊
exponentialHalfGrowth = two₊ ⁻¹₊


private
  module ℚOrder =
    OrderedCommRingTheory ℚOrderedCommRing

  fromNat-mono : ∀ {m n} →
    m ℕ.≤ n → ℚ.fromNat m ℚ.≤ ℚ.fromNat n
  fromNat-mono {m} {n} (difference , difference+m≡n) =
    subst (ℚ.fromNat m ℚ.≤_)
      (ℚ.ℕ+→ℚ+ difference m
      ∙ cong (λ k → ℚ.fromNat k) difference+m≡n)
      (subst2 ℚ._≤_
        (ℚ.+IdR (ℚ.fromNat m))
        (ℚ.+Comm (ℚ.fromNat m) (ℚ.fromNat difference))
        (ℚOrder.+MonoL≤
          0 (ℚ.fromNat difference) (ℚ.fromNat m)
          (ℚ.0≤pos difference (1+ zero))))

  exponentialRationalCoefficient-positive : ∀ n →
    0 ℚ.< exponentialRationalCoefficient n
  exponentialRationalCoefficient-positive n =
    snd (exponentialRationalFactorial n ⁻¹₊)

  exponentialRationalCoefficient-nonnegative : ∀ n →
    0 ℚ.≤ exponentialRationalCoefficient n
  exponentialRationalCoefficient-nonnegative n =
    ℚ.<Weaken≤ 0 (exponentialRationalCoefficient n)
      (exponentialRationalCoefficient-positive n)

  exponentialRationalCoefficient-inverse-step : ∀ n →
    exponentialRationalCoefficient (suc n)
      ≡
    fst (exponentialPositiveNatural n ⁻¹₊)
      ℚ.· exponentialRationalCoefficient n
  exponentialRationalCoefficient-inverse-step n =
    cong fst
      (sym
        (ℚInv.invℚ₊Dist·
          (exponentialPositiveNatural n) (exponentialRationalFactorial n)))

  inverseSuccessorFromTwo≤half : ∀ n →
    fst (exponentialPositiveNatural (suc n) ⁻¹₊) ℚ.≤ halfℚ
  inverseSuccessorFromTwo≤half n =
    ℚInv.invℚ≤invℚ
      (exponentialPositiveNatural (suc n)) two₊
      (fromNat-mono
        (ℕ.suc-≤-suc (ℕ.suc-≤-suc ℕ.zero-≤)))

  halfNonnegative : 0 ℚ.≤ halfℚ
  halfNonnegative =
    ℚ.<Weaken≤ 0 halfℚ (snd exponentialHalfGrowth)

  exponentialRationalCoefficient-halfGrowth : ∀ n →
    exponentialRationalCoefficient n
      ℚ.≤
    ℚ.fromNat 2 ℚ.· powℚ halfℚ n
  exponentialRationalCoefficient-halfGrowth zero =
    subst2 ℚ._≤_
      (sym exponentialRationalCoefficient-zero)
      (sym (ℚ.·IdR (ℚ.fromNat 2)))
      (fromNat-mono (ℕ.suc-≤-suc ℕ.zero-≤))
  exponentialRationalCoefficient-halfGrowth (suc zero) =
    subst2 ℚ._≤_ (sym leftPath) (sym rightPath)
      (ℚ.isRefl≤ 1)
    where
    leftPath : exponentialRationalCoefficient (suc zero) ≡ 1
    leftPath =
      sym (ℚ.·IdL (exponentialRationalCoefficient (suc zero)))
      ∙ exponentialRationalCoefficient-suc zero
      ∙ exponentialRationalCoefficient-zero

    rightPath :
      ℚ.fromNat 2 ℚ.· powℚ halfℚ (suc zero) ≡ 1
    rightPath =
      cong (ℚ.fromNat 2 ℚ.·_)
        (ℚ.·IdR halfℚ)
      ∙ ℚInv.x·invℚ₊[x] two₊
  exponentialRationalCoefficient-halfGrowth (suc (suc n)) =
    subst2 ℚ._≤_
      (sym (exponentialRationalCoefficient-inverse-step (suc n)))
      growthStepPath
      productBound
    where
    previous : ℚ
    previous = exponentialRationalCoefficient (suc n)

    previousBound : ℚ
    previousBound =
      ℚ.fromNat 2 ℚ.· powℚ halfℚ (suc n)

    productBound :
      fst (exponentialPositiveNatural (suc n) ⁻¹₊) ℚ.· previous
        ℚ.≤ halfℚ ℚ.· previousBound
    productBound =
      ℚOrder.·Mono≤
        (fst (exponentialPositiveNatural (suc n) ⁻¹₊)) halfℚ
        previous previousBound
        halfNonnegative
        (exponentialRationalCoefficient-nonnegative (suc n))
        (inverseSuccessorFromTwo≤half n)
        (exponentialRationalCoefficient-halfGrowth (suc n))

    growthStepPath :
      halfℚ ℚ.· previousBound
        ≡
      ℚ.fromNat 2 ℚ.· powℚ halfℚ (suc (suc n))
    growthStepPath =
      ℚ.·Assoc
        halfℚ (ℚ.fromNat 2) (powℚ halfℚ (suc n))
      ∙ cong (ℚ._· powℚ halfℚ (suc n))
          (ℚ.·Comm halfℚ (ℚ.fromNat 2))
      ∙ sym
          (ℚ.·Assoc
            (ℚ.fromNat 2) halfℚ (powℚ halfℚ (suc n)))


exponentialCoefficientGrowthHalf :
  CoefficientGrowthBound
    two₊ exponentialHalfGrowth exponentialCoefficients
exponentialCoefficientGrowthHalf n =
  subst
    (_≤ℝ rat (ℚ.fromNat 2) · powℝ (rat halfℚ) n)
    (sym absolutePath)
    (subst
      (rat (exponentialRationalCoefficient n) ≤ℝ_)
      (sym upperPath)
      (invEq
        (rat≤rat≃
          (exponentialRationalCoefficient n)
          (ℚ.fromNat 2 ℚ.· powℚ halfℚ n))
        (exponentialRationalCoefficient-halfGrowth n)))
  where
  absolutePath :
    absℝ (exponentialCoefficients n)
      ≡ rat (exponentialRationalCoefficient n)
  absolutePath =
    abs-rat (exponentialRationalCoefficient n)
    ∙ cong rat
        (ℚOrder.0≤→abs≡id
          (exponentialRationalCoefficient n)
          (exponentialRationalCoefficient-nonnegative n))

  upperPath :
    rat (ℚ.fromNat 2) · powℝ (rat halfℚ) n
      ≡
    rat (ℚ.fromNat 2 ℚ.· powℚ halfℚ n)
  upperPath =
    cong (rat (ℚ.fromNat 2) ·_) (pow-rat halfℚ n)
    ∙ mul-rat (ℚ.fromNat 2) (powℚ halfℚ n)


-- The parameter b selects the positive natural base B = suc b.  Unlike the
-- compact radius-two estimate above, this family gives a geometric
-- majorant at every explicitly bounded rational radius.
exponentialCoefficientGrowthFactorial : ∀ b →
  CoefficientGrowthBound
    (exponentialFactorialGrowthBound b)
    (exponentialFactorialDecay b)
    exponentialCoefficients
exponentialCoefficientGrowthFactorial b n =
  subst
    (_≤ℝ
      rat (fst (exponentialFactorialGrowthBound b)) ·
        powℝ (rat (fst (exponentialFactorialDecay b))) n)
    (sym absolutePath)
    (subst
      (rat (exponentialRationalCoefficient n) ≤ℝ_)
      (sym upperPath)
      (invEq
        (rat≤rat≃
          (exponentialRationalCoefficient n)
          (fst (exponentialFactorialGrowthBound b) ℚ.·
            powℚ (fst (exponentialFactorialDecay b)) n))
        (exponentialRationalCoefficient-factorialGrowth b n)))
  where
  absolutePath :
    absℝ (exponentialCoefficients n)
      ≡ rat (exponentialRationalCoefficient n)
  absolutePath =
    abs-rat (exponentialRationalCoefficient n)
    ∙ cong rat
        (ℚOrder.0≤→abs≡id
          (exponentialRationalCoefficient n)
          (exponentialRationalCoefficient-nonnegative n))

  upperPath :
    rat (fst (exponentialFactorialGrowthBound b)) ·
        powℝ (rat (fst (exponentialFactorialDecay b))) n
      ≡
    rat
      (fst (exponentialFactorialGrowthBound b) ℚ.·
        powℚ (fst (exponentialFactorialDecay b)) n)
  upperPath =
    cong (rat (fst (exponentialFactorialGrowthBound b)) ·_)
      (pow-rat (fst (exponentialFactorialDecay b)) n)
    ∙ mul-rat
        (fst (exponentialFactorialGrowthBound b))
        (powℚ (fst (exponentialFactorialDecay b)) n)


exponentialFactorialRadiusLessThanOne : ∀ b radius →
  fst radius ℚ.< fst (exponentialPositiveNatural b) →
  fst (growthRadius (exponentialFactorialDecay b) radius) ℚ.< 1
exponentialFactorialRadiusLessThanOne b radius radius<base =
  subst (ℚ._< 1)
    (ℚ.·Comm
      (fst radius)
      (fst (exponentialFactorialDecay b)))
    (fst
      (ℚInv.x<y≃x/y<1
        (fst radius) (exponentialPositiveNatural b))
      radius<base)


exponentialHalfRadiusLessThanOne : ∀ radius →
  fst radius ℚ.< ℚ.fromNat 2 →
  fst (growthRadius exponentialHalfGrowth radius) ℚ.< 1
exponentialHalfRadiusLessThanOne radius radius<two =
  subst (ℚ._< 1)
    (ℚ.·Comm (fst radius) halfℚ)
    (fst (ℚInv.x<y≃x/y<1 (fst radius) two₊) radius<two)


exponentialPowerSeriesIsAbsolutelyCauchyWithinTwo : ∀ radius x →
  absℝ x ≤ℝ rat (fst radius) →
  fst radius ℚ.< ℚ.fromNat 2 →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms exponentialCoefficients x)
exponentialPowerSeriesIsAbsolutelyCauchyWithinTwo
    radius x absx≤radius radius<two =
  powerSeriesIsAbsolutelyCauchyByGrowth
    two₊ exponentialHalfGrowth radius exponentialCoefficients x
    exponentialCoefficientGrowthHalf
    absx≤radius
    (exponentialHalfRadiusLessThanOne radius radius<two)


exponentialPowerSeriesIsCauchyWithinTwo : ∀ radius x →
  absℝ x ≤ℝ rat (fst radius) →
  fst radius ℚ.< ℚ.fromNat 2 →
  IsCauchySeries (powerSeriesTerms exponentialCoefficients x)
exponentialPowerSeriesIsCauchyWithinTwo
    radius x absx≤radius radius<two =
  absoluteCauchySeriesIsCauchy
    (powerSeriesTerms exponentialCoefficients x)
    (exponentialPowerSeriesIsAbsolutelyCauchyWithinTwo
      radius x absx≤radius radius<two)


exponentialPowerSeriesSummableWithinTwo : ∀ radius x →
  absℝ x ≤ℝ rat (fst radius) →
  fst radius ℚ.< ℚ.fromNat 2 →
  PowerSeriesSummableAt exponentialCoefficients x
exponentialPowerSeriesSummableWithinTwo
    radius x absx≤radius radius<two =
  absoluteCauchySeriesIsSummable
    (powerSeriesTerms exponentialCoefficients x)
    (exponentialPowerSeriesIsAbsolutelyCauchyWithinTwo
      radius x absx≤radius radius<two)


exponentialPowerSeriesHasSumWithinTwo : ∀ radius x →
  (absx≤radius : absℝ x ≤ℝ rat (fst radius)) →
  (radius<two : fst radius ℚ.< ℚ.fromNat 2) →
  HasSum (powerSeriesTerms exponentialCoefficients x)
    (powerSeriesValue exponentialCoefficients x
      (exponentialPowerSeriesSummableWithinTwo
        radius x absx≤radius radius<two))
exponentialPowerSeriesHasSumWithinTwo
    radius x absx≤radius radius<two =
  seriesSumHasSum
    (powerSeriesTerms exponentialCoefficients x)
    (exponentialPowerSeriesSummableWithinTwo
      radius x absx≤radius radius<two)


exponentialPowerSeriesUniformlyCauchyWithinTwo : ∀ radius →
  fst radius ℚ.< ℚ.fromNat 2 →
  UniformlyCauchySeries
    (ClosedRationalRadius radius)
    (powerSeriesOnClosedRadius exponentialCoefficients radius)
exponentialPowerSeriesUniformlyCauchyWithinTwo radius radius<two =
  powerSeriesUniformlyCauchyByGrowth
    two₊ exponentialHalfGrowth radius exponentialCoefficients
    exponentialCoefficientGrowthHalf
    (exponentialHalfRadiusLessThanOne radius radius<two)


exponentialPowerSeriesClosedRadiusSummableWithinTwo : ∀ radius →
  fst radius ℚ.< ℚ.fromNat 2 →
  ∀ point →
  PowerSeriesSummableAt exponentialCoefficients (fst point)
exponentialPowerSeriesClosedRadiusSummableWithinTwo
    radius radius<two point =
  uniformlyCauchySeriesSummableAt
    (exponentialPowerSeriesUniformlyCauchyWithinTwo
      radius radius<two)
    point


exponentialPowerSeriesIsAbsolutelyCauchyWithinNaturalBound :
  ∀ b radius x →
  absℝ x ≤ℝ rat (fst radius) →
  fst radius ℚ.< fst (exponentialPositiveNatural b) →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms exponentialCoefficients x)
exponentialPowerSeriesIsAbsolutelyCauchyWithinNaturalBound
    b radius x absx≤radius radius<base =
  powerSeriesIsAbsolutelyCauchyByGrowth
    (exponentialFactorialGrowthBound b)
    (exponentialFactorialDecay b)
    radius exponentialCoefficients x
    (exponentialCoefficientGrowthFactorial b)
    absx≤radius
    (exponentialFactorialRadiusLessThanOne b radius radius<base)


exponentialPowerSeriesIsCauchyWithinNaturalBound :
  ∀ b radius x →
  absℝ x ≤ℝ rat (fst radius) →
  fst radius ℚ.< fst (exponentialPositiveNatural b) →
  IsCauchySeries (powerSeriesTerms exponentialCoefficients x)
exponentialPowerSeriesIsCauchyWithinNaturalBound
    b radius x absx≤radius radius<base =
  absoluteCauchySeriesIsCauchy
    (powerSeriesTerms exponentialCoefficients x)
    (exponentialPowerSeriesIsAbsolutelyCauchyWithinNaturalBound
      b radius x absx≤radius radius<base)


exponentialPowerSeriesSummableWithinNaturalBound :
  ∀ b radius x →
  absℝ x ≤ℝ rat (fst radius) →
  fst radius ℚ.< fst (exponentialPositiveNatural b) →
  PowerSeriesSummableAt exponentialCoefficients x
exponentialPowerSeriesSummableWithinNaturalBound
    b radius x absx≤radius radius<base =
  absoluteCauchySeriesIsSummable
    (powerSeriesTerms exponentialCoefficients x)
    (exponentialPowerSeriesIsAbsolutelyCauchyWithinNaturalBound
      b radius x absx≤radius radius<base)


exponentialPowerSeriesHasSumWithinNaturalBound :
  ∀ b radius x →
  (absx≤radius : absℝ x ≤ℝ rat (fst radius)) →
  (radius<base :
    fst radius ℚ.< fst (exponentialPositiveNatural b)) →
  HasSum (powerSeriesTerms exponentialCoefficients x)
    (powerSeriesValue exponentialCoefficients x
      (exponentialPowerSeriesSummableWithinNaturalBound
        b radius x absx≤radius radius<base))
exponentialPowerSeriesHasSumWithinNaturalBound
    b radius x absx≤radius radius<base =
  seriesSumHasSum
    (powerSeriesTerms exponentialCoefficients x)
    (exponentialPowerSeriesSummableWithinNaturalBound
      b radius x absx≤radius radius<base)


exponentialPowerSeriesUniformlyCauchyWithinNaturalBound :
  ∀ b radius →
  fst radius ℚ.< fst (exponentialPositiveNatural b) →
  UniformlyCauchySeries
    (ClosedRationalRadius radius)
    (powerSeriesOnClosedRadius exponentialCoefficients radius)
exponentialPowerSeriesUniformlyCauchyWithinNaturalBound
    b radius radius<base =
  powerSeriesUniformlyCauchyByGrowth
    (exponentialFactorialGrowthBound b)
    (exponentialFactorialDecay b)
    radius exponentialCoefficients
    (exponentialCoefficientGrowthFactorial b)
    (exponentialFactorialRadiusLessThanOne b radius radius<base)


exponentialPowerSeriesClosedRadiusSummableWithinNaturalBound :
  ∀ b radius →
  fst radius ℚ.< fst (exponentialPositiveNatural b) →
  ∀ point →
  PowerSeriesSummableAt exponentialCoefficients (fst point)
exponentialPowerSeriesClosedRadiusSummableWithinNaturalBound
    b radius radius<base point =
  uniformlyCauchySeriesSummableAt
    (exponentialPowerSeriesUniformlyCauchyWithinNaturalBound
      b radius radius<base)
    point
