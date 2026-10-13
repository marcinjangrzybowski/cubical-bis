module Cubical.Analysis.Complex.Continuity.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Mappings
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Conjugation
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Continuity

fromℝ-isContinuous : isContinuous (ℝPremetricSpace .snd) fromℝ (ℂPremetricSpace .snd)
fromℝ-isContinuous = pairℂ-isContinuous (ℝPremetricSpace .snd) (idfun ℝ) (λ _ → 0ℝ)
  (snd (idᶜ {M = ℝPremetricSpace})) (constantRealMapIsContinuous (ℝPremetricSpace .snd) 0ℝ)

conjugate-isContinuous : isContinuous (ℂPremetricSpace .snd) conjugate (ℂPremetricSpace .snd)
conjugate-isContinuous = pairℂ-isContinuous (ℂPremetricSpace .snd) re (λ z → - im z)
  reℂ-isContinuous (snd ((-_ , neg-isContinuous) ∘C (im , imℂ-isContinuous)))

naturalPowerℂ-isContinuous : ∀ n →
  isContinuous (ℂPremetricSpace .snd) (λ z → z ^ℂ n) (ℂPremetricSpace .snd)
naturalPowerℂ-isContinuous zero = constantℂ-isContinuous (ℂPremetricSpace .snd) 1ℂ
naturalPowerℂ-isContinuous (suc n) = mulOfComplexContinuous (ℂPremetricSpace .snd)
  (idfun ℂ) (λ z → z ^ℂ n) (snd (idᶜ {M = ℂPremetricSpace})) (naturalPowerℂ-isContinuous n)
