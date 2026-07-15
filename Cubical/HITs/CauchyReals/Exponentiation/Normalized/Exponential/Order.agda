module Cubical.HITs.CauchyReals.Exponentiation.Normalized.Exponential.Order where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition
open import Cubical.HITs.CauchyReals.Exponentiation.Normalized.Exponential.Base public

opaque
  one<eBase : 1 <ᵣ fst eBase
  one<eBase =
    subst (1 <ᵣ_)
      (cong fst (sym (normalizedBase-spec two one<two)))
      (isTrans≡<ᵣ _ _ _ (sym (^ᵣ0 two))
        (^ᵣ-mon-str two one<two 0
          (fst (invℝ₊ lnTwo₊)) (snd (invℝ₊ lnTwo₊))))
    where
    lnTwo₊ : ℝ₊
    lnTwo₊ = ln two , 1<a→0<ln[a] two one<two

realExpStrictMonotone : ∀ x y → x <ᵣ y →
  fst (realExp x) <ᵣ fst (realExp y)
realExpStrictMonotone = ^ᵣ-mon-str eBase one<eBase
