module Cubical.HITs.CauchyReals.Exponentiation.Logarithm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.RationalsImports
open import Cubical.HITs.CauchyReals.ExponentiationMore

opaque
  ln-injective : ∀ x y → ln x ≡ ln y → x ≡ y
  ln-injective = inj-ln

ln-strictMonotone-<1 :
  ∀ (x y : ℝ₊) →
  fst y <ᵣ 1 →
  fst x <ᵣ fst y →
  ln x <ᵣ ln y
ln-strictMonotone-<1 x y y<1 x<y =
  <ᵣ-ᵣ _ _ (subst2 _<ᵣ_
    (ln-inv y)
    (ln-inv x)
    (ln-mon-str-1< (invℝ₊ y) (invℝ₊ x)
      (fst (1/x<1≃1<x (invℝ₊ y))
        (isTrans≡<ᵣ _ _ _ (cong fst (invℝ₊Invol y)) y<1))
      (invEq (invℝ₊-<-invℝ₊ _ _) x<y)))
