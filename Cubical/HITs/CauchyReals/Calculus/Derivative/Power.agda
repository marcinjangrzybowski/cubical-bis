module Cubical.HITs.CauchyReals.Calculus.Derivative.Power where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base
open import Cubical.HITs.CauchyReals.Analysis.Uniform using
  ( bounded-id
  ; bounded-^ⁿ
  ; IsUContinuousℙ^ⁿ
  )
open import Cubical.HITs.CauchyReals.Foundation.Rationals

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- Previous name: uDerivativeOfℙ^n, when this proof lived in
-- ExponentialSeriesDerivative.
uDerivativeOfℙ-^ⁿ : ∀ a b → rat a <ᵣ rat b
  → ∀ n
  → uDerivativeOfℙ (intervalℙ (rat a) (rat b)) , (λ x _ → x ^ⁿ (suc n))
    is λ x _ → fromNat (suc n) ·ᵣ (x ^ⁿ n)
uDerivativeOfℙ-^ⁿ a b a<b zero =
  subst2 (uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,_is_)
    (funExt₂ λ x _ → sym (·IdR x))
    (funExt₂ λ _ _ → sym (·IdLᵣ 1))
    (uDerivativeℙ-id (intervalℙ (rat a) (rat b)))
uDerivativeOfℙ-^ⁿ a b a<b (suc n) =
 subst2 (uDerivativeOfℙ (intervalℙ (rat a) (rat b)) ,_is_)
    (funExt₂ λ x _ → ·ᵣComm (x ^ⁿ suc n) x)
    (funExt₂ λ x _ →
      cong₂ _+ᵣ_
        (sym (·ᵣAssoc _ _ _)
          ∙ cong (fromNat (suc n) ·ᵣ_) (·ᵣComm (x ^ⁿ n) x))
        refl
      ∙ sym (·DistR+ _ _ _)
      ∙ cong (_·ᵣ (x ^ⁿ suc n))
          (+ᵣComm _ _
           ∙ +ᵣ-rat _ _
           ∙ cong rat (ℚ.ℕ+→ℚ+ 1 (suc n))))
    (uDerivativeOfℙ· (rat a) (rat b) a<b
      (λ x _ → x ^ⁿ (suc n))
      (λ x _ → x)
      (λ x _ → fromNat (suc n) ·ᵣ (x ^ⁿ n))
      (λ _ _ → 1)
      (bounded-^ⁿ a b (<ᵣWeaken≤ᵣ (rat a) (rat b) a<b) (suc n))
      (bounded-id a b)
      (IsUContinuousℙ^ⁿ a b (<ᵣWeaken≤ᵣ (rat a) (rat b) a<b) (suc n))
      (1 , λ _ _ → ≡ᵣWeaken≤ᵣ (absᵣ 1) 1 (absᵣ-rat 1))
      (uDerivativeOfℙ-^ⁿ a b a<b n)
      (uDerivativeℙ-id (intervalℙ (rat a) (rat b))))

DerivativeOfℙ-^ⁿ : ∀ a b → rat a <ᵣ rat b
  → ∀ n
  → DerivativeOfℙ (intervalℙ (rat a) (rat b)) , (λ x _ → x ^ⁿ (suc n))
    is λ x _ → fromNat (suc n) ·ᵣ (x ^ⁿ n)
DerivativeOfℙ-^ⁿ a b a<b n =
  uDerivativeOfℙ→DerivativeOfℙ
    (intervalℙ (rat a) (rat b))
    (λ x _ → x ^ⁿ (suc n))
    (λ x _ → fromNat (suc n) ·ᵣ (x ^ⁿ n))
    (uDerivativeOfℙ-^ⁿ a b a<b n)
