module Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Translation.Representation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition using (addPres≤L)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Center
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Representation
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Canonical
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Domain
open import Cubical.Analysis.Complex.Series.PowerSeries.Primitive.Translation.Coefficients

module _ (coefficients : ComplexSequence) (outer : ℝ) (outerNonnegative : 0ℝ ≤ℝ outer)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer))
  (constant center : ℂ) (inside : normℂ center <ℝ outer) where
  private
    integrated translated : ComplexSequence
    integrated = formalPrimitiveℂ constant coefficients
    translated = complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside
    native : Real.IsCauchySeries (complexPowerSeriesMajorant integrated outer)
    native = formalPrimitiveℂMajorantIsCauchy constant coefficients outer outerNonnegative witness
    newConstant : ℂ
    newConstant = translatedPrimitiveConstant coefficients outer outerNonnegative witness constant center inside

  -- Transport any supplied original primitive sum. Values remain intrinsic
  -- to the convergence domain; no total ambient extension is assumed.
  opaque
    translatedPrimitiveHasSum : ∀ increment → normℂ center + normℂ increment <ℝ outer → ∀ value →
      HasComplexSum (powerSeriesTermsℂ integrated (center +ℂ increment)) value →
      HasComplexSum (powerSeriesTermsℂ (formalPrimitiveℂ newConstant translated) increment) value
    translatedPrimitiveHasSum increment fits value originalSum = subst
      (λ c → HasComplexSum (powerSeriesTermsℂ c increment) value)
      (translatedPrimitiveCoefficients coefficients outer outerNonnegative witness constant center inside)
      (translatedTaylorHasSum integrated outer native center inside increment fits value originalSum)

  module _ (radius : ℝ) (nonnegative : 0ℝ ≤ℝ radius) (fits : normℂ center + radius <ℝ outer) where
    private
      localNative : Real.IsCauchySeries (complexPowerSeriesMajorant translated radius)
      localNative = translatedTaylorMajorantIsCauchy coefficients outer witness center inside radius nonnegative fits
      pointFits : ∀ (point : ClosedComplexNormRadius radius) → normℂ center + normℂ (fst point) <ℝ outer
      pointFits point = ≤<ℝ-trans (normℂ center + normℂ (fst point)) (normℂ center + radius) outer
        (addPres≤L (normℂ (fst point)) radius (normℂ center) (snd point)) fits

    translatedPrimitiveDomainPoint : ClosedComplexNormRadius radius → ClosedComplexNormRadius outer
    translatedPrimitiveDomainPoint point = center +ℂ fst point ,
      <ℝ-weaken (normℂ (center +ℂ fst point)) outer
        (translatedEvaluationInside center (fst point) outer (pointFits point))

    opaque
      translatedPrimitiveDomainValueAgrees : ∀ point →
        closedComplexPowerSeriesPrimitive translated radius localNative newConstant nonnegative point ≡
        closedComplexPowerSeriesPrimitive coefficients outer witness constant outerNonnegative (translatedPrimitiveDomainPoint point)
      translatedPrimitiveDomainValueAgrees point = complexSumUnique
        (powerSeriesTermsℂ (formalPrimitiveℂ newConstant translated) (fst point))
        (closedComplexPowerSeriesPrimitive translated radius localNative newConstant nonnegative point)
        (closedComplexPowerSeriesPrimitive coefficients outer witness constant outerNonnegative (translatedPrimitiveDomainPoint point))
        (closedComplexPowerSeriesPrimitiveHasSum translated radius localNative newConstant nonnegative point)
        (translatedPrimitiveHasSum (fst point) (pointFits point)
          (closedComplexPowerSeriesPrimitive coefficients outer witness constant outerNonnegative (translatedPrimitiveDomainPoint point))
          (closedComplexPowerSeriesPrimitiveHasSum coefficients outer witness constant outerNonnegative (translatedPrimitiveDomainPoint point)))

      translatedPrimitiveDomainValuesAgree :
        closedComplexPowerSeriesPrimitive translated radius localNative newConstant nonnegative ≡
        closedComplexPowerSeriesPrimitive coefficients outer witness constant outerNonnegative ∘ translatedPrimitiveDomainPoint
      translatedPrimitiveDomainValuesAgree = funExt translatedPrimitiveDomainValueAgrees
