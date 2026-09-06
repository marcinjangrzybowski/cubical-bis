module Cubical.Analysis.Real.Series.Geometric.Real where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base using (ℚ; fromNat)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Density
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Geometric.Base
open import Cubical.Analysis.Real.Series.Geometric.BoundedReal

private
  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing


-- One rational bound works at every precision. Eliminating its truncated
-- existence into a native Cauchy witness does not require countable choice.
mereRationalContractionBound : ∀ q → absℝ q <ℝ 1ℝ →
  ∃[ r ∈ ℚ ] RationalContractionBound q r
mereRationalContractionBound q inside =
  PT.map makeBound (denseℚinℝ (absℝ q) 1ℝ inside)
  where
  makeBound : (Σ[ r ∈ ℚ ] (absℝ q <ℝ rat r) × (rat r <ℝ 1ℝ)) →
    Σ[ r ∈ ℚ ] RationalContractionBound q r
  makeBound (r , above , below) =
    r , <ℝ-weaken (absℝ q) (rat r) above
      , subst (ℚ._< 1) (sym (ℚOrder.0≤→abs≡id r
          (ℚ.<Weaken≤ 0 r (<ℝ→<ℚ 0 r
            (≤<ℝ-trans 0ℝ (absℝ q) (rat r) (absNonnegative q) above)))))
          (<ℝ→<ℚ r 1 below)


realGeometricSeriesIsCauchy : ∀ q → absℝ q <ℝ 1ℝ →
  IsCauchySeries (geometricTerms q)
realGeometricSeriesIsCauchy q inside =
  PT.rec squash₁
    (λ { (r , bound) → realGeometricSeriesIsCauchyByRationalBound q r bound })
    (mereRationalContractionBound q inside)


realGeometricSeriesSummable : ∀ q → absℝ q <ℝ 1ℝ →
  Summable (geometricTerms q)
realGeometricSeriesSummable q inside =
  cauchySeriesIsSummable (geometricTerms q)
    (realGeometricSeriesIsCauchy q inside)


realGeometricPowersTendToZero : ∀ q → absℝ q <ℝ 1ℝ →
  isLimitSequence (geometricTerms q) 0ℝ
realGeometricPowersTendToZero q inside =
  summableTermsTendToZero (geometricTerms q)
    (realGeometricSeriesSummable q inside)
