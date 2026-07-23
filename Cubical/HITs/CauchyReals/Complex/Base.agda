module Cubical.HITs.CauchyReals.Complex.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness using (isSetℝ)


ℂ : Type
ℂ = ℝ × ℝ


complex : ℝ → ℝ → ℂ
complex x y = x , y


re : ℂ → ℝ
re = fst


im : ℂ → ℝ
im = snd


isSetℂ : isSet ℂ
isSetℂ = isSet× isSetℝ isSetℝ


ℂ≡ : ∀ {z w : ℂ} → re z ≡ re w → im z ≡ im w → z ≡ w
ℂ≡ p q = cong₂ _,_ p q


ℂ≡-re : ∀ {z w : ℂ} → z ≡ w → re z ≡ re w
ℂ≡-re = cong re


ℂ≡-im : ∀ {z w : ℂ} → z ≡ w → im z ≡ im w
ℂ≡-im = cong im

