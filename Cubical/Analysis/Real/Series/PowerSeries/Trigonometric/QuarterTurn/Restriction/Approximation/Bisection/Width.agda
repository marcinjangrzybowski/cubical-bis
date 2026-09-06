module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Width where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as ℕ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Algebra.Scalar.Compatibility
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Geometric.Base
open import Cubical.Analysis.Real.Series.Geometric.Rational
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry


iteratedHalving : ℕ → ℝ → ℝ
iteratedHalving zero value = value
iteratedHalving (suc n) value = quarterTurnHalf ⋆ iteratedHalving n value


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


opaque
  iteratedHalving-asGeometric : ∀ n value →
    iteratedHalving n value ≡
    geometricTerms (rat quarterTurnHalf) n · value
  iteratedHalving-asGeometric zero value = sym (mulIdL value)
  iteratedHalving-asGeometric (suc n) value =
    scalar-as-mul quarterTurnHalf (iteratedHalving n value)
    ∙ cong (rat quarterTurnHalf ·_) (iteratedHalving-asGeometric n value)
    ∙ mulAssoc (rat quarterTurnHalf)
        (geometricTerms (rat quarterTurnHalf) n) value


  iteratedHalvingTendsToZero : ∀ value →
    isLimitSequence (λ n → iteratedHalving n value) 0ℝ
  iteratedHalvingTendsToZero value =
    subst (λ sequence → isLimitSequence sequence 0ℝ)
      (sym (funExt (λ n → iteratedHalving-asGeometric n value)))
      (subst (isLimitSequence
          (λ n → geometricTerms (rat quarterTurnHalf) n · value))
        (ℝRing.0LeftAnnihilates value)
        (mulPresIsLimitSequence
          (rationalGeometricPowersTendToZero quarterTurnHalf
            (ℚ.<Weaken≤ _ _ 1/2∈ℚ.0<1/2)
            (subst (quarterTurnHalf ℚ.≤_) (sym halfℚPath)
              (ℚ.isRefl≤ quarterTurnHalf)))
          (constantIsLimitSequence value)))


  -- A finite stage can be selected inside truncation at any requested scale.
  iteratedHalvingEventuallySmall : ∀ value (tolerance : ℚ₊) →
    ∥ Σ[ n ∈ ℕ ] iteratedHalving n value <ℝ rat (fst tolerance) ∥₁
  iteratedHalvingEventuallySmall value tolerance =
    PT.map
      (λ { (n , close) → n ,
        ≤<ℝ-trans (iteratedHalving n value)
          (absℝ (iteratedHalving n value)) (rat (fst tolerance))
          (leAbs (iteratedHalving n value))
          (subst (_<ℝ rat (fst tolerance))
            (cong absℝ (subZero (iteratedHalving n value)))
            (closeness→absDifference< (iteratedHalving n value) 0ℝ tolerance
              (close n ℕ.≤-refl))) })
      (iteratedHalvingTendsToZero value tolerance)


  iteratedHalvingProductEventuallySmall : ∀ value factor (tolerance : ℚ₊) →
    ∥ Σ[ n ∈ ℕ ]
        iteratedHalving n value · factor <ℝ rat (fst tolerance) ∥₁
  iteratedHalvingProductEventuallySmall value factor tolerance =
    PT.map
      (λ { (n , close) → n ,
        ≤<ℝ-trans (iteratedHalving n value · factor)
          (absℝ (iteratedHalving n value · factor)) (rat (fst tolerance))
          (leAbs (iteratedHalving n value · factor))
          (subst (_<ℝ rat (fst tolerance))
            (cong absℝ (subZero (iteratedHalving n value · factor)))
            (closeness→absDifference<
              (iteratedHalving n value · factor) 0ℝ tolerance
              (close n ℕ.≤-refl))) })
      (subst (isLimitSequence (λ n → iteratedHalving n value · factor))
        (ℝRing.0LeftAnnihilates factor)
        (mulPresIsLimitSequence
          (iteratedHalvingTendsToZero value)
          (constantIsLimitSequence factor)) tolerance)
