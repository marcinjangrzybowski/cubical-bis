module Cubical.HITs.CauchyReals.Complex.Analysis.Sequence.Subtraction where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence.Mapping
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence.Addition.Limit
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence.Addition.Cauchy


subConverges :
  (a b : ComplexSequence) → (l m : ℂ) →
  ConvergesToℂ a l → ConvergesToℂ b m →
  ConvergesToℂ (λ n → a n +ℂ (-ℂ b n)) (l +ℂ (-ℂ m))
subConverges a b l m a→l b→m =
  addConverges a (λ n → -ℂ b n) l (-ℂ m)
    a→l (negConverges b m b→m)


subCauchy : (a b : ComplexSequence) →
  IsCauchySequenceℂ a → IsCauchySequenceℂ b →
  IsCauchySequenceℂ (λ n → a n +ℂ (-ℂ b n))
subCauchy a b a-cauchy b-cauchy =
  addCauchy a (λ n → -ℂ b n)
    a-cauchy (negCauchy b b-cauchy)
