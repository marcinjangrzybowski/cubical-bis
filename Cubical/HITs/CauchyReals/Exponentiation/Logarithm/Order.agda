module Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.StrictMonotonicity
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Injectivity

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
