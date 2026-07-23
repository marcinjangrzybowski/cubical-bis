module Cubical.HITs.CauchyReals.Complex.Inverse.Definition where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Inverse using
  (_＃_; invℝ)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Conjugation
open import Cubical.HITs.CauchyReals.Complex.NormSquared
open import Cubical.HITs.CauchyReals.Complex.Apartness


infixl 7 _／ℂ[_,_]


normSqApart : ∀ z → 0ℂ #ℂ z → 0 ＃ normSq z
normSqApart z 0#z = inl (0#ℂ→0<normSq 0#z)


invℂ : (z : ℂ) → 0ℂ #ℂ z → ℂ
invℂ z 0#z =
  fromℝ (invℝ (normSq z) (normSqApart z 0#z)) ·ℂ conj z


invℂ-proof-irrelevant : ∀ z (p q : 0ℂ #ℂ z) →
  invℂ z p ≡ invℂ z q
invℂ-proof-irrelevant z p q = cong (invℂ z) (isProp#ℂ _ _ p q)


_／ℂ[_,_] : ℂ → (z : ℂ) → 0ℂ #ℂ z → ℂ
x ／ℂ[ z , 0#z ] = x ·ℂ invℂ z 0#z
