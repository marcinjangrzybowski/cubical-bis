module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.AtZero where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent


opaque
  sinℝ-at-tangentDomainZero :
    sinℝ (fst tangentDomainZero) ≡ 0ℝ
  sinℝ-at-tangentDomainZero =
    cong sinℝ tangentDomainZero-coordinate
    ∙ sinℝ-zero-for-tangent


  cosℝ-at-tangentDomainZero :
    cosℝ (fst tangentDomainZero) ≡ 1ℝ
  cosℝ-at-tangentDomainZero =
    cong cosℝ tangentDomainZero-coordinate
    ∙ cosℝ-zero-for-tangent


tanℝ-zero : tanℝ tangentDomainZero ≡ 0ℝ
tanℝ-zero =
  tanℝ-zero-from-sine-zero
    tangentDomainZero sinℝ-at-tangentDomainZero


secℝ-zero : secℝ tangentDomainZero ≡ 1ℝ
secℝ-zero =
  secℝ-one-from-cosine-one
    tangentDomainZero cosℝ-at-tangentDomainZero
