module Cubical.HITs.CauchyReals.Exponentiation.Normalized.Exponential.Base where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition using (ln; _^ᵣ_)
open import Cubical.HITs.CauchyReals.Exponentiation.Normalized.Base public
open import Cubical.HITs.CauchyReals.Exponentiation.Normalized.BaseLaw public

two : ℝ₊
two = fromNat 2

one<two : 1 <ᵣ fst two
one<two = decℚ<ᵣ?

eBase : ℝ₊
eBase = normalizedBase two one<two

ln-eBase : ln eBase ≡ 1
ln-eBase = ln-normalizedBase two one<two

realExp : ℝ → ℝ₊
realExp = eBase ^ᵣ_
