module Cubical.HITs.CauchyReals.Complex.Analysis.Sequence.Cauchy where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.OrderedCommRing.Properties
open OrderedCommRingTheory ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.Relation.Premetric.Base

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Metric.Base
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence


converges→cauchy : ∀ sequence limit →
  ConvergesToℂ sequence limit →
  IsCauchySequenceℂ sequence
converges→cauchy sequence limit (N , converges) =
  (λ ε → N (ε /2₊)) ,
  λ ε m n N≤m N≤n →
    PremetricStr.subst≈ (snd ℂPremetricSpace)
      (sequence m) (sequence n)
      {ε = (ε /2₊) +₊ (ε /2₊)} {ε' = ε}
      (1/2∈ℚ./2+/2≡id (fst ε))
      (PremetricStr.isTriangular≈ (snd ℂPremetricSpace)
        (sequence m) limit (sequence n)
        (ε /2₊) (ε /2₊)
        (converges (ε /2₊) m N≤m)
        (PremetricStr.isSym≈ (snd ℂPremetricSpace)
          (sequence n) limit (ε /2₊)
          (converges (ε /2₊) n N≤n)))
