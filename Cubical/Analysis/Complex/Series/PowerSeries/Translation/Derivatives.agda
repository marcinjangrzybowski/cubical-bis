module Cubical.Analysis.Complex.Series.PowerSeries.Translation.Derivatives where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Domain.Radius
open import Cubical.Analysis.Complex.Domain.Radius.Translation
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative.Interior
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Center
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Representation
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Translation
open import Cubical.Analysis.Complex.Calculus.Derivative.Tower
open import Cubical.Analysis.Complex.Calculus.Derivative.Tower.OpenSubspace

-- Reexpansion commutes with every derivative. The two native derivative
-- towers agree by intrinsic uniqueness on the translated open ball; no
-- termwise rearrangement of an infinite differentiated double sum is needed.
module _ (coefficients : ComplexSequence) (outer : ℝ)
  (witness : Real.IsCauchySeries (complexPowerSeriesMajorant coefficients outer))
  (center : ℂ) (inside : normℂ center <ℝ outer) (radius : ℝ)
  (nonnegative : 0ℝ ≤ℝ radius) (fits : normℂ center + radius <ℝ outer) where
  private
    translated : ComplexSequence
    translated = complexPowerSeriesTaylorCoefficientsAtCenter coefficients outer witness center inside

    native : Real.IsCauchySeries (complexPowerSeriesMajorant translated radius)
    native = translatedTaylorMajorantIsCauchy coefficients outer witness center inside radius nonnegative fits

    fitsWeak : normℂ center + radius ≤ℝ outer
    fitsWeak = <ℝ-weaken (normℂ center + radius) outer fits

  translatedTaylorDomainPoint : OpenComplexNormRadius radius → OpenComplexNormRadius outer
  translatedTaylorDomainPoint = translateOpenComplexNormRadius center radius outer fitsWeak

  private
    originalValues : ℕ → OpenComplexNormRadius radius → ℂ
    originalValues order point = openInteriorPowerSeriesDerivatives coefficients outer witness order (translatedTaylorDomainPoint point)

    originalTower : IsComplexDerivativeTowerAlong
      (OpenComplexNormRadiusPremetricSpace radius .snd) fst originalValues
    originalTower order point = untranslateComplexDerivativeCoordinateAlongAt
      (OpenComplexNormRadiusPremetricSpace radius .snd) fst (originalValues order) center
      (originalValues (suc order) point) point
      (pullbackComplexDerivativeAlong (OpenComplexNormRadiusPremetricSpace radius .snd)
        (OpenComplexNormRadiusPremetricSpace outer .snd) fst
        (openInteriorPowerSeriesDerivatives coefficients outer witness order)
        (openInteriorPowerSeriesDerivatives coefficients outer witness (suc order)) translatedTaylorDomainPoint
        (snd (NE→C (translateOpenComplexNormRadiusNE center radius outer fitsWeak)))
        (openInteriorPowerSeriesDerivativeTower coefficients outer witness order) point)

  opaque
    translatedTaylorDerivativeTowerAgrees :
      openInteriorPowerSeriesDerivatives translated radius native ≡ originalValues
    translatedTaylorDerivativeTowerAgrees = openSubspaceComplexDerivativeTowerUnique
      (OpenComplexNormRadiusPredicate radius) (openComplexNormRadiusIsOpen radius)
      (openInteriorPowerSeriesDerivatives translated radius native) originalValues
      (openInteriorPowerSeriesDerivativeTower translated radius native) originalTower
      (funExt λ point → complexSumUnique (powerSeriesTermsℂ translated (fst point))
        (openInteriorPowerSeriesDerivatives translated radius native 0 point) (originalValues 0 point)
        (openInteriorPowerSeriesDerivativeSums translated radius native 0 point)
        (translatedTaylorHasSum coefficients outer witness center inside (fst point)
          (<ℝ-trans (normℂ center + normℂ (fst point)) (normℂ center + radius) outer
            (<ℝ-addL (normℂ (fst point)) radius (normℂ center) (snd point)) fits)
          (originalValues 0 point)
          (openInteriorPowerSeriesDerivativeSums coefficients outer witness 0 (translatedTaylorDomainPoint point))))

    translatedTaylorDerivativeHasCanonicalSum : ∀ order point →
      HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ order translated) (fst point))
        (openInteriorPowerSeriesDerivatives coefficients outer witness order (translatedTaylorDomainPoint point))
    translatedTaylorDerivativeHasCanonicalSum order point = subst
      (HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ order translated) (fst point)))
      (cong (λ tower → tower order point) translatedTaylorDerivativeTowerAgrees)
      (openInteriorPowerSeriesDerivativeSums translated radius native order point)

    translatedTaylorDerivativeHasSum : ∀ order point value →
      HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ order coefficients)
        (fst (translatedTaylorDomainPoint point))) value →
      HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ order translated) (fst point)) value
    translatedTaylorDerivativeHasSum order point value originalSum = subst
      (HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ order translated) (fst point)))
      (openInteriorPowerSeriesDerivativeAgrees coefficients outer witness order
        (translatedTaylorDomainPoint point) value originalSum)
      (translatedTaylorDerivativeHasCanonicalSum order point)
