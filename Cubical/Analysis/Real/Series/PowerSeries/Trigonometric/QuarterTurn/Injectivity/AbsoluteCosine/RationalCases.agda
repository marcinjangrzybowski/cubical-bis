module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine.RationalCases where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.Data.Rationals.Order.AbsoluteValue using (absCases)
open import Cubical.Data.Sum using (_⊎_)

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open OrderedCommRingTheory ℚOrderedCommRing using (abs)


rationalNegation : ℚ → ℚ
rationalNegation =
  OrderedCommRingStr.-_ (ℚOrderedCommRing .snd)


rationalAbsolute : ℚ → ℚ
rationalAbsolute = abs


opaque
  rationalAbsoluteCases : ∀ q →
    (rationalAbsolute q ≡ rationalNegation q) ⊎
    (rationalAbsolute q ≡ q)
  rationalAbsoluteCases = absCases
