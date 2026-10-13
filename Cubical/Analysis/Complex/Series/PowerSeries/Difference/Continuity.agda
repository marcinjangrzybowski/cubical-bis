module Cubical.Analysis.Complex.Series.PowerSeries.Difference.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Continuity
open import Cubical.Analysis.Complex.Continuity.Algebra
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
import Cubical.Analysis.Complex.Series.PowerSeries.Difference.Algebra as Algebra

open import Cubical.Analysis.Complex.Series.PowerSeries.Difference

opaque
  private
    powerAlongContinuous : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
      (y : A → ℂ) → isContinuous source y (ℂPremetricSpace .snd) → ∀ n →
      isContinuous source (λ p → y p ^ℂ n) (ℂPremetricSpace .snd)
    powerAlongContinuous source y cy n =
      snd (_∘C_ {M = _ , source} {N = ℂPremetricSpace} {O = ℂPremetricSpace}
        ((λ z → z ^ℂ n) , naturalPowerℂ-isContinuous n) (y , cy))

powerDifferenceFactorℂIsContinuous : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) (x y : A → ℂ) →
  isContinuous source x (ℂPremetricSpace .snd) → isContinuous source y (ℂPremetricSpace .snd) →
  ∀ n → isContinuous source (λ p → powerDifferenceFactorℂ (x p) (y p) n) (ℂPremetricSpace .snd)
powerDifferenceFactorℂIsContinuous source x y cx cy zero =
  subst (λ f → isContinuous source f (ℂPremetricSpace .snd))
    (sym (funExt (λ p → powerDifferenceFactorℂ-zero (x p) (y p)))) (constantℂ-isContinuous source 1ℂ)
powerDifferenceFactorℂIsContinuous source x y cx cy (suc n) =
  subst (λ f → isContinuous source f (ℂPremetricSpace .snd))
    (sym (funExt (λ p → powerDifferenceFactorℂ-step (x p) (y p) n)))
    (addOfComplexContinuous source (λ p → y p ^ℂ suc n) (λ p → x p ·ℂ powerDifferenceFactorℂ (x p) (y p) n)
      (powerAlongContinuous source y cy (suc n))
      (mulOfComplexContinuous source x (λ p → powerDifferenceFactorℂ (x p) (y p) n) cx
        (powerDifferenceFactorℂIsContinuous source x y cx cy n)))

powerSeriesDifferenceFactorℂIsContinuous : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) coefficients (x y : A → ℂ) →
  isContinuous source x (ℂPremetricSpace .snd) → isContinuous source y (ℂPremetricSpace .snd) →
  ∀ n → isContinuous source (λ p → powerSeriesDifferenceFactorℂ coefficients (x p) (y p) n) (ℂPremetricSpace .snd)
powerSeriesDifferenceFactorℂIsContinuous source coefficients x y cx cy n =
  mulOfComplexContinuous source (λ _ → coefficients (suc n)) (λ p → powerDifferenceFactorℂ (x p) (y p) n)
    (constantℂ-isContinuous source (coefficients (suc n))) (powerDifferenceFactorℂIsContinuous source x y cx cy n)
