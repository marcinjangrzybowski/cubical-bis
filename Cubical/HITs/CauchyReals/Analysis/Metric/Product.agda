module Cubical.HITs.CauchyReals.Analysis.Metric.Product where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Base using (PremetricSpace)
open import Cubical.Relation.Premetric.Instances.Product

open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric


ℝ²PremetricSpace : PremetricSpace ℓ-zero ℓ-zero
ℝ²PremetricSpace =
  PremetricProduct ℝPremetricSpace ℝPremetricSpace
