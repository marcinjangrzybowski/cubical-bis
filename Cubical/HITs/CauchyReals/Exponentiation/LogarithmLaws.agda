module Cubical.HITs.CauchyReals.Exponentiation.LogarithmLaws where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.RationalsImports hiding (_^_)
open import Cubical.HITs.CauchyReals.ExponentiationMore
open import Cubical.HITs.CauchyReals.Exponentiation.NormalizedExponential

opaque
  ln-mul : ∀ x y → ln x +ᵣ ln y ≡ ln (x ₊·ᵣ y)
  ln-mul x y =
    sym (ln-realExp (ln x +ᵣ ln y))
    ∙ cong ln
        (^ᵣ+ eBase (ln x) (ln y)
         ∙ cong₂ _₊·ᵣ_ (realExp-ln x) (realExp-ln y))

  lnStrictMonotone : ∀ x y → fst x <ᵣ fst y → ln x <ᵣ ln y
  lnStrictMonotone x y x<y =
    <-o+-cancel _ _ _
      (subst2 _<ᵣ_
        (sym (ln-mul factor x))
        (sym (ln-mul factor y))
        (ln-mon-str-1< (factor ₊·ᵣ x) (factor ₊·ᵣ y)
          one<factorTimesX factorTimesX<factorTimesY))
    where
    factor : ℝ₊
    factor = two ₊·ᵣ invℝ₊ x

    one<factorTimesX : 1 <ᵣ fst (factor ₊·ᵣ x)
    one<factorTimesX =
      isTrans<≡ᵣ 1 2 (fst (factor ₊·ᵣ x))
        decℚ<ᵣ? (sym ([x/₊y]·yᵣ 2 x))

    factorTimesX<factorTimesY :
      fst (factor ₊·ᵣ x) <ᵣ fst (factor ₊·ᵣ y)
    factorTimesX<factorTimesY = <ᵣ-o·ᵣ _ _ factor x<y
