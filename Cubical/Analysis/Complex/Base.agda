module Cubical.Analysis.Complex.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Analysis.Real.Base using (ℝ; isSetℝ)

-- Both coordinates use Analysis's native sequential completion.
ℂ : Type₀
ℂ = ℝ × ℝ

complex : ℝ → ℝ → ℂ
complex x y = x , y

re im : ℂ → ℝ
re = fst
im = snd

isSetℂ : isSet ℂ
isSetℂ = isSet× isSetℝ isSetℝ

ℂ≡ : ∀ {z w : ℂ} → re z ≡ re w → im z ≡ im w → z ≡ w
ℂ≡ p q = cong₂ _,_ p q
