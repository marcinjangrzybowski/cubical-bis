module Cubical.Analysis.Complex.Domain.RightHalfPlane where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Foundations.Powerset
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Domain.OpenInterval
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric

-- Intrinsic domain: the positivity proof travels with each point. Its
-- premetric and inclusion are the generic library subspace construction.
RightHalfPlanePredicate : ℙ ℂ
RightHalfPlanePredicate = predicatePreimage re (LowerOpenHalfLinePredicate 0ℝ)

ComplexRightHalfPlane : Type₀
ComplexRightHalfPlane = Σ[ z ∈ ℂ ] 0ℝ <ℝ re z

RightHalfPlanePremetricSpace : PremetricSpace ℓ-zero ℓ-zero
RightHalfPlanePremetricSpace = PremetricSubspace ℂPremetricSpace RightHalfPlanePredicate

rightHalfPlaneInclusionNE : NE[ RightHalfPlanePremetricSpace , ℂPremetricSpace ]
rightHalfPlaneInclusionNE = subspaceInclusionNE ℂPremetricSpace RightHalfPlanePredicate

rightHalfPlaneIsOpen : IsOpenPredicate (ℂPremetricSpace .snd) RightHalfPlanePredicate
rightHalfPlaneIsOpen = continuousPreimageIsOpen re (LowerOpenHalfLinePredicate 0ℝ)
  reℂ-isContinuous (lowerOpenHalfLineIsOpen 0ℝ)
