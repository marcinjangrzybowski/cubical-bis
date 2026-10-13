module Cubical.Analysis.Complex.Sequence.Continuous where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Sequence

-- Use the generic premetric theorem, keeping the coordinate-limit interface.
-- Continuity preserves a supplied limit; it does not select Cauchy moduli.
opaque
  continuousComplexMapPreservesLimit : (f : ℂ → ℂ) →
    isContinuous (ℂPremetricSpace .snd) f (ℂPremetricSpace .snd) →
    ∀ {z l} → IsComplexLimit z l → IsComplexLimit (f ∘ z) (f l)
  continuousComplexMapPreservesLimit f continuous {z} {l} limit =
    premetricLimit→complexLimit (f ∘ z) (f l)
      (C→seqContinuous {M = ℂPremetricSpace} {N = ℂPremetricSpace}
        (f , continuous) z l (complexLimit→premetricLimit z l limit))
