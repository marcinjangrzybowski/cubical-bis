module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.CosineFactor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Bounds


opaque
  quarterTurnMidpointCosinePositive : ∀ quarter x y →
    IsFirstPositiveCosineZero quarter →
    (- quarter) ≤ℝ x → y ≤ℝ quarter → x <ℝ y →
    0ℝ <ℝ cosℝ (quarterTurnMidpoint x y)
  quarterTurnMidpointCosinePositive
      quarter x y characterization negative-quarter≤x y≤quarter x<y =
    characterizedCosine-positive-inside
      quarter characterization (quarterTurnMidpoint x y)
      (fst midpoint-inside) (snd midpoint-inside)
    where
    midpoint-inside :
      ((- quarter) <ℝ quarterTurnMidpoint x y)
      × (quarterTurnMidpoint x y <ℝ quarter)
    midpoint-inside =
      quarterTurnMidpoint-inside quarter x y
        negative-quarter≤x y≤quarter x<y
