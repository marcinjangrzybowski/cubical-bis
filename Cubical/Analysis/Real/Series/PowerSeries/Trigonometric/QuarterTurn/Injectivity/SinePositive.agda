module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.SinePositive where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
  using (0ℝ; addIdL; addIdR; addAssoc)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Phase
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine


private
  shiftedBack : ℝ → ℝ → ℝ
  shiftedBack quarter x = x + (- quarter)


opaque
  characterizedSine-positive-to-quarter : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    IsFirstPositiveCosineZero quarter →
    ∀ x → 0ℝ <ℝ x → x ≤ℝ quarter →
    0ℝ <ℝ sinℝ x
  characterizedSine-positive-to-quarter
      quarter positive-quarter characterization x zero<x x≤quarter =
    subst (0ℝ <ℝ_)
      (sym sine-as-cosine)
      cosine-positive
    where
    negative-quarter<zero : (- quarter) <ℝ 0ℝ
    negative-quarter<zero =
      subst ((- quarter) <ℝ_)
        negZero
        (<ℝ-neg 0ℝ quarter
          (firstPositiveCosineZero-positive characterization))

    shifted-lower : (- quarter) <ℝ shiftedBack quarter x
    shifted-lower =
      subst (_<ℝ shiftedBack quarter x)
        (addIdL (- quarter))
        (<ℝ-addR 0ℝ x (- quarter) zero<x)

    shifted-upper : shiftedBack quarter x <ℝ quarter
    shifted-upper =
      subst (shiftedBack quarter x <ℝ_)
        (addIdR quarter)
        (≤<ℝ-add
          x quarter (- quarter) 0ℝ
          x≤quarter negative-quarter<zero)

    cosine-positive :
      0ℝ <ℝ cosℝ (shiftedBack quarter x)
    cosine-positive =
      characterizedCosine-positive-inside
        quarter characterization (shiftedBack quarter x)
        shifted-lower shifted-upper

    unshift : shiftedBack quarter x + quarter ≡ x
    unshift =
      sym (addAssoc x (- quarter) quarter)
      ∙ cong (x +_) (addInvL quarter)
      ∙ addIdR x

    sine-as-cosine :
      sinℝ x ≡ cosℝ (shiftedBack quarter x)
    sine-as-cosine =
      cong sinℝ (sym unshift)
      ∙ sinℝ-add-quarterTurn
          quarter positive-quarter (shiftedBack quarter x)
