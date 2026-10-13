module Cubical.Analysis.Complex.Domain.Radius.Translation where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Domain.Radius

-- The usual radius condition is sufficient for translating an open norm
-- ball into another one. Equality at the radius boundary is permitted.
translateOpenComplexNormRadius : ∀ center inner outer → normℂ center + inner ≤ℝ outer →
  OpenComplexNormRadius inner → OpenComplexNormRadius outer
translateOpenComplexNormRadius center inner outer fits (increment , inside) = center +ℂ increment ,
  <≤ℝ-trans (normℂ (center +ℂ increment)) (normℂ center + inner) outer
    (≤<ℝ-trans (normℂ (center +ℂ increment)) (normℂ center + normℂ increment) (normℂ center + inner)
      (normℂ-triangle center increment) (<ℝ-addL (normℂ increment) inner (normℂ center) inside)) fits

translateOpenComplexNormRadiusNE : ∀ center inner outer (fits : normℂ center + inner ≤ℝ outer) →
  NE[ OpenComplexNormRadiusPremetricSpace inner , OpenComplexNormRadiusPremetricSpace outer ]
fst (translateOpenComplexNormRadiusNE center inner outer fits) = translateOpenComplexNormRadius center inner outer fits
IsNonExpanding.pres≈ (snd (translateOpenComplexNormRadiusNE center inner outer fits)) x y ε =
  addℂ-presClosenessL center (fst x) (fst y) ε
