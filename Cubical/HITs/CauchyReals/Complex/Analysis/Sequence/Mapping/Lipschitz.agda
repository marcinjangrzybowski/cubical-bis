module Cubical.HITs.CauchyReals.Complex.Analysis.Sequence.Mapping.Lipschitz where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Inverse

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Metric.Base
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence


mapConvergesLipschitzWith :
  ∀ L (f : ℂ → ℂ) →
  IsLipschitzWith
    (snd ℂPremetricSpace) f
    (snd ℂPremetricSpace) L →
  (sequence : ComplexSequence) → (limit : ℂ) →
  ConvergesToℂ sequence limit →
  ConvergesToℂ
    (λ n → f (sequence n)) (f limit)
mapConvergesLipschitzWith
  L f f-lipschitz sequence limit (N , converges) =
  (λ ε → N (ε ₊／₊ L)) ,
  λ ε n N≤n →
    PremetricStr.subst≈
      (snd ℂPremetricSpace)
      (f (sequence n)) (f limit)
      {ε = L ·₊ (ε ₊／₊ L)}
      {ε' = ε}
      (·／ L ε)
      (IsLipschitzWith.pres≈ f-lipschitz
        (sequence n) limit
        (ε ₊／₊ L)
        (converges (ε ₊／₊ L) n N≤n))


mapCauchyLipschitzWith :
  ∀ L (f : ℂ → ℂ) →
  IsLipschitzWith
    (snd ℂPremetricSpace) f
    (snd ℂPremetricSpace) L →
  (sequence : ComplexSequence) →
  IsCauchySequenceℂ sequence →
  IsCauchySequenceℂ
    (λ n → f (sequence n))
mapCauchyLipschitzWith
  L f f-lipschitz sequence (N , cauchy) =
  (λ ε → N (ε ₊／₊ L)) ,
  λ ε m n N≤m N≤n →
    PremetricStr.subst≈
      (snd ℂPremetricSpace)
      (f (sequence m)) (f (sequence n))
      {ε = L ·₊ (ε ₊／₊ L)}
      {ε' = ε}
      (·／ L ε)
      (IsLipschitzWith.pres≈ f-lipschitz
        (sequence m) (sequence n)
        (ε ₊／₊ L)
        (cauchy (ε ₊／₊ L)
          m n N≤m N≤n))
