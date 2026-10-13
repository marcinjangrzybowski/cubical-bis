module Cubical.Analysis.Complex.Series.PowerSeries.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (zero)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Continuity
open import Cubical.Analysis.Complex.Continuity.Algebra
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Operations

powerSeriesTermsℂ : ComplexSequence → ℂ → ComplexSequence
powerSeriesTermsℂ coefficients z n = coefficients n ·ℂ (z ^ℂ n)

ComplexPowerSeriesSummableAt : ComplexSequence → ℂ → Type₀
ComplexPowerSeriesSummableAt coefficients z = ComplexSummable (powerSeriesTermsℂ coefficients z)

powerSeriesValueℂ : ∀ coefficients z → ComplexPowerSeriesSummableAt coefficients z → ℂ
powerSeriesValueℂ coefficients z = seriesSumℂ (powerSeriesTermsℂ coefficients z)

powerSeriesValueℂIndependent : ∀ coefficients z (p q : ComplexPowerSeriesSummableAt coefficients z) →
  powerSeriesValueℂ coefficients z p ≡ powerSeriesValueℂ coefficients z q
powerSeriesValueℂIndependent coefficients z = seriesSumℂIndependent (powerSeriesTermsℂ coefficients z)

powerSeriesTermsℂ-zero : ∀ coefficients z → powerSeriesTermsℂ coefficients z zero ≡ coefficients zero
powerSeriesTermsℂ-zero coefficients z = ·ℂIdR (coefficients zero)

powerSeriesTermsℂ-add : ∀ a b z n → powerSeriesTermsℂ (λ k → a k +ℂ b k) z n ≡
  powerSeriesTermsℂ a z n +ℂ powerSeriesTermsℂ b z n
powerSeriesTermsℂ-add a b z n = ·ℂComm (a n +ℂ b n) (z ^ℂ n)
  ∙ ·ℂDistR+ (z ^ℂ n) (a n) (b n)
  ∙ cong₂ _+ℂ_ (·ℂComm (z ^ℂ n) (a n)) (·ℂComm (z ^ℂ n) (b n))

powerSeriesTermsℂ-scale : ∀ c coefficients z n → powerSeriesTermsℂ (scaleComplexSeries c coefficients) z n ≡
  scaleComplexSeries c (powerSeriesTermsℂ coefficients z) n
powerSeriesTermsℂ-scale c coefficients z n = sym (·ℂAssoc c (coefficients n) (z ^ℂ n))

-- Every finite term is continuous along a supplied continuous coordinate.
-- This avoids committing the series API to a particular closed-ball type.
powerSeriesTermℂIsContinuous : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
  (coordinate : A → ℂ) coefficients → isContinuous source coordinate (ℂPremetricSpace .snd) →
  ∀ n → isContinuous source (λ x → powerSeriesTermsℂ coefficients (coordinate x) n) (ℂPremetricSpace .snd)
powerSeriesTermℂIsContinuous source coordinate coefficients continuous n =
  mulOfComplexContinuous source (λ _ → coefficients n) (λ x → coordinate x ^ℂ n)
    (constantℂ-isContinuous source (coefficients n))
    (snd (((λ z → z ^ℂ n) , naturalPowerℂ-isContinuous n) ∘C (coordinate , continuous)))
