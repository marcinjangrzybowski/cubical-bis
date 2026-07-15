module Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.Rationals as ℚ using (ℚ)

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Power
open import Cubical.HITs.CauchyReals.Exponentiation.RationalPower.Core
open import Cubical.HITs.CauchyReals.Foundation.Rationals

private
  intervalPos : ∀ {a b : ℚ} {x : ℝ}
    → 0 <ᵣ rat a
    → x ∈ intervalℙ (rat a) (rat b)
    → 0 <ᵣ x
  intervalPos 0<a x∈ = isTrans<≤ᵣ _ _ _ 0<a (fst x∈)

-- Previous name: positive-power cases of derivative-^ℤ were proved through
-- the old pointwise derivative API in ExponentiationDer.
uDerivativeOfℙ-₊^ⁿ : ∀ a b
  → (0<a : 0 <ᵣ rat a)
  → (a<b : rat a <ᵣ rat b)
  → ∀ n
  → uDerivativeOfℙ (intervalℙ (rat a) (rat b))
      , (λ x x∈ → fst ((x , intervalPos 0<a x∈) ₊^ⁿ (suc n)))
    is λ x x∈ →
      fromNat (suc n) ·ᵣ fst ((x , intervalPos 0<a x∈) ₊^ⁿ n)
uDerivativeOfℙ-₊^ⁿ a b 0<a a<b n =
  uDerivativeOfℙ-^ⁿ a b a<b n

DerivativeOfℙ-₊^ⁿ : ∀ a b
  → (0<a : 0 <ᵣ rat a)
  → (a<b : rat a <ᵣ rat b)
  → ∀ n
  → DerivativeOfℙ (intervalℙ (rat a) (rat b))
      , (λ x x∈ → fst ((x , intervalPos 0<a x∈) ₊^ⁿ (suc n)))
    is λ x x∈ →
      fromNat (suc n) ·ᵣ fst ((x , intervalPos 0<a x∈) ₊^ⁿ n)
DerivativeOfℙ-₊^ⁿ a b 0<a a<b n =
  DerivativeOfℙ-^ⁿ a b a<b n

-- Previous name: positive branch of derivative-^ℤ.
uDerivativeOfℙ-^ℤ-pos : ∀ a b
  → (0<a : 0 <ᵣ rat a)
  → (a<b : rat a <ᵣ rat b)
  → ∀ n
  → uDerivativeOfℙ (intervalℙ (rat a) (rat b))
      , (λ x x∈ → fst ((x , intervalPos 0<a x∈) ^ℤ pos (suc n)))
    is λ x x∈ →
      fromNat (suc n) ·ᵣ fst ((x , intervalPos 0<a x∈) ^ℤ pos n)
uDerivativeOfℙ-^ℤ-pos a b 0<a a<b n =
  uDerivativeOfℙ-₊^ⁿ a b 0<a a<b n

DerivativeOfℙ-^ℤ-pos : ∀ a b
  → (0<a : 0 <ᵣ rat a)
  → (a<b : rat a <ᵣ rat b)
  → ∀ n
  → DerivativeOfℙ (intervalℙ (rat a) (rat b))
      , (λ x x∈ → fst ((x , intervalPos 0<a x∈) ^ℤ pos (suc n)))
    is λ x x∈ →
      fromNat (suc n) ·ᵣ fst ((x , intervalPos 0<a x∈) ^ℤ pos n)
DerivativeOfℙ-^ℤ-pos a b 0<a a<b n =
  DerivativeOfℙ-₊^ⁿ a b 0<a a<b n
