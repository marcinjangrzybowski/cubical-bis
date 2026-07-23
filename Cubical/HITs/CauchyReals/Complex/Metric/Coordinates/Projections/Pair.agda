module Cubical.HITs.CauchyReals.Complex.Metric.Coordinates.Projections.Pair where

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.Metric.Product

open import Cubical.HITs.CauchyReals.Complex.Metric.Base
open import Cubical.HITs.CauchyReals.Complex.Metric.Coordinates.Projections.Real
open import Cubical.HITs.CauchyReals.Complex.Metric.Coordinates.Projections.Imaginary


ℂ→ℝ²NE : NE[ ℂPremetricSpace , ℝ²PremetricSpace ]
ℂ→ℝ²NE = pairNE reℂNE imℂNE
