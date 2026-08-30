module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform.Reindex where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform


-- Uniform Cauchyness is contravariant in the parameter space.  Keeping this
-- elementary fact separate avoids reproving cutoff transport for every
-- restriction, reparametrisation, or bounded-domain inclusion.

uniformlyCauchySeriesPrecompose : ∀ {ℓ ℓ'}
  (X : Type ℓ) (Y : Type ℓ')
  (terms : Y → RealSequence) →
  UniformlyCauchySeries Y terms →
  (map : X → Y) →
  UniformlyCauchySeries X (terms ∘ map)
uniformlyCauchySeriesPrecompose X Y terms uniform map ε =
  PT.map
    (λ (N , close) →
      N , λ x m n N≤m N≤n →
        close (map x) m n N≤m N≤n)
    (uniform ε)


uniformlyAbsolutelyCauchySeriesPrecompose : ∀ {ℓ ℓ'}
  (X : Type ℓ) (Y : Type ℓ')
  (terms : Y → RealSequence) →
  UniformlyAbsolutelyCauchySeries Y terms →
  (map : X → Y) →
  UniformlyAbsolutelyCauchySeries X (terms ∘ map)
uniformlyAbsolutelyCauchySeriesPrecompose X Y terms uniform map =
  uniformlyCauchySeriesPrecompose
    X Y (λ y → Abs.absℝ ∘ terms y)
    uniform map


-- Pointwise equality of the term sequences transports one common cutoff.
-- The equality is stated at sequence level so clients can establish it by
-- `funExt` once, rather than transporting every partial sum separately.

uniformlyCauchySeriesPresPointwisePath : ∀ {ℓ}
  (X : Type ℓ) (left right : X → RealSequence) →
  (∀ x → left x ≡ right x) →
  UniformlyCauchySeries X left →
  UniformlyCauchySeries X right
uniformlyCauchySeriesPresPointwisePath X left right path uniform =
  subst (UniformlyCauchySeries X)
    (funExt path) uniform


uniformlyCauchySeriesPathInvariant : ∀ {ℓ}
  (X : Type ℓ) (left right : X → RealSequence) →
  (∀ x → left x ≡ right x) →
  UniformlyCauchySeries X left ≡
  UniformlyCauchySeries X right
uniformlyCauchySeriesPathInvariant X left right path =
  cong (UniformlyCauchySeries X) (funExt path)


uniformlyAbsolutelyCauchySeriesPresPointwisePath : ∀ {ℓ}
  (X : Type ℓ) (left right : X → RealSequence) →
  (∀ x → left x ≡ right x) →
  UniformlyAbsolutelyCauchySeries X left →
  UniformlyAbsolutelyCauchySeries X right
uniformlyAbsolutelyCauchySeriesPresPointwisePath
  X left right path uniform =
  subst (UniformlyAbsolutelyCauchySeries X)
    (funExt path) uniform


uniformSeriesValuePrecompose : ∀ {ℓ ℓ'}
  (X : Type ℓ) (Y : Type ℓ')
  (terms : Y → RealSequence)
  (uniform : UniformlyCauchySeries Y terms)
  (map : X → Y) (x : X) →
  uniformSeriesValue X (terms ∘ map)
      (uniformlyCauchySeriesPrecompose X Y terms uniform map) x
    ≡
  uniformSeriesValue Y terms uniform (map x)
uniformSeriesValuePrecompose X Y terms uniform map x =
  seriesSumIndependent (terms (map x))
    (uniformlyCauchySeriesSummableAt
      X (terms ∘ map)
      (uniformlyCauchySeriesPrecompose X Y terms uniform map) x)
    (uniformlyCauchySeriesSummableAt
      Y terms uniform (map x))


-- A specified uniform limit also restricts along every map of parameter
-- spaces.  This complements Cauchy reindexing when a later argument needs
-- the actual common tail around an already chosen value function.

uniformlyConvergesSeriesPrecompose : ∀ {ℓ ℓ'}
  (X : Type ℓ) (Y : Type ℓ')
  (terms : Y → RealSequence) (value : Y → Real.ℝ) →
  UniformlyConvergesSeries Y terms value →
  (map : X → Y) →
  UniformlyConvergesSeries X (terms ∘ map) (value ∘ map)
uniformlyConvergesSeriesPrecompose
  X Y terms value converges map ε =
  PT.map
    (λ (N , close) →
      N , λ x n N≤n → close (map x) n N≤n)
    (converges ε)
