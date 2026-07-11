module Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Extras where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset



open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous

open import Cubical.HITs.CauchyReals.ArcSin.Positive.Properties.Inverse public
IsContinuousWithPred-ᵣ : ∀ P f → IsContinuousWithPred P f →
  IsContinuousWithPred P λ x x∈ → -ᵣ (f x x∈)
IsContinuousWithPred-ᵣ P f fc =
  IsContinuousWP∘' P _ _ IsContinuous-ᵣ fc
