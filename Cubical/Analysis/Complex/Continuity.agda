module Cubical.Analysis.Complex.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Mappings
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric

constantℂ-isContinuous : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A) (z : ℂ) →
  isContinuous source (λ _ → z) (ℂPremetricSpace .snd)
constantℂ-isContinuous source z = pairℂ-isContinuous source (λ _ → re z) (λ _ → im z)
  (constantRealMapIsContinuous source (re z)) (constantRealMapIsContinuous source (im z))

module _ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A) where
  reOfComplexContinuous : (f : A → ℂ) → isContinuous source f (ℂPremetricSpace .snd) →
    isContinuous source (re ∘ f) (ℝPremetricSpace .snd)
  reOfComplexContinuous f fc = snd ((re , reℂ-isContinuous) ∘C (f , fc))

  imOfComplexContinuous : (f : A → ℂ) → isContinuous source f (ℂPremetricSpace .snd) →
    isContinuous source (im ∘ f) (ℝPremetricSpace .snd)
  imOfComplexContinuous f fc = snd ((im , imℂ-isContinuous) ∘C (f , fc))

  addOfComplexContinuous : (f g : A → ℂ) →
    isContinuous source f (ℂPremetricSpace .snd) → isContinuous source g (ℂPremetricSpace .snd) →
    isContinuous source (λ x → f x +ℂ g x) (ℂPremetricSpace .snd)
  addOfComplexContinuous f g fc gc = pairℂ-isContinuous source _ _
    (addOfContinuousIsContinuous source (re ∘ f) (re ∘ g)
      (reOfComplexContinuous f fc) (reOfComplexContinuous g gc))
    (addOfContinuousIsContinuous source (im ∘ f) (im ∘ g)
      (imOfComplexContinuous f fc) (imOfComplexContinuous g gc))

  negOfComplexContinuous : (f : A → ℂ) → isContinuous source f (ℂPremetricSpace .snd) →
    isContinuous source (λ x → -ℂ f x) (ℂPremetricSpace .snd)
  negOfComplexContinuous f fc = pairℂ-isContinuous source _ _
    (snd ((-_ , neg-isContinuous) ∘C (re ∘ f , reOfComplexContinuous f fc)))
    (snd ((-_ , neg-isContinuous) ∘C (im ∘ f , imOfComplexContinuous f fc)))

  subOfComplexContinuous : (f g : A → ℂ) →
    isContinuous source f (ℂPremetricSpace .snd) → isContinuous source g (ℂPremetricSpace .snd) →
    isContinuous source (λ x → f x -ℂ g x) (ℂPremetricSpace .snd)
  subOfComplexContinuous f g fc gc = addOfComplexContinuous f (λ x → -ℂ g x) fc
    (negOfComplexContinuous g gc)

  mulOfComplexContinuous : (f g : A → ℂ) →
    isContinuous source f (ℂPremetricSpace .snd) → isContinuous source g (ℂPremetricSpace .snd) →
    isContinuous source (λ x → f x ·ℂ g x) (ℂPremetricSpace .snd)
  mulOfComplexContinuous f g fc gc = pairℂ-isContinuous source _ _
    (addOfContinuousIsContinuous source _ _ rr
      (snd ((-_ , neg-isContinuous) ∘C ((λ x → im (f x) · im (g x)) , ii))))
    (addOfContinuousIsContinuous source _ _ ri ir)
    where
    rr = mulOfContinuousIsContinuous source (re ∘ f) (re ∘ g)
      (reOfComplexContinuous f fc) (reOfComplexContinuous g gc)
    ii = mulOfContinuousIsContinuous source (im ∘ f) (im ∘ g)
      (imOfComplexContinuous f fc) (imOfComplexContinuous g gc)
    ri = mulOfContinuousIsContinuous source (re ∘ f) (im ∘ g)
      (reOfComplexContinuous f fc) (imOfComplexContinuous g gc)
    ir = mulOfContinuousIsContinuous source (im ∘ f) (re ∘ g)
      (imOfComplexContinuous f fc) (reOfComplexContinuous g gc)

leftMultiplyℂ-isContinuous : ∀ c → isContinuous (ℂPremetricSpace .snd) (c ·ℂ_) (ℂPremetricSpace .snd)
leftMultiplyℂ-isContinuous c = mulOfComplexContinuous (ℂPremetricSpace .snd) (λ _ → c) (idfun ℂ)
  (constantℂ-isContinuous (ℂPremetricSpace .snd) c) (snd (idᶜ {M = ℂPremetricSpace}))
