module Cubical.HITs.CauchyReals.Complex.Analysis.Sequence.Mapping.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat as ℕ

open import Cubical.Relation.Premetric.Base

open import Cubical.HITs.CauchyReals.Complex.Metric.Base
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence


constantConverges : ∀ c → ConvergesToℂ (λ (_ : ℕ) → c) c
constantConverges c =
  (λ _ → zero) ,
  λ ε _ _ → PremetricStr.isRefl≈ (snd ℂPremetricSpace) c ε


constantCauchy : ∀ c → IsCauchySequenceℂ (λ (_ : ℕ) → c)
constantCauchy c =
  (λ _ → zero) ,
  λ ε _ _ _ _ → PremetricStr.isRefl≈ (snd ℂPremetricSpace) c ε
