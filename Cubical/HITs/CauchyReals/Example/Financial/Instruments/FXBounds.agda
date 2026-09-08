{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Instruments.FXBounds where

open import Cubical.HITs.CauchyReals.Example.Financial.Instruments.FXSwap public
open import Cubical.HITs.CauchyReals.Example.Financial.Core.Bounds public
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

record FXBox : Type₀ where
  constructor fx-box
  field
    spotBounds domesticBounds foreignBounds : Bound
open FXBox public

record InBox (box : FXBox) (state : FXState) : Type₀ where
  constructor in-box
  field
    spotWithin : InInterval (spotBounds box) (spot state)
    domesticWithin : InInterval (domesticBounds box) (domesticDiscount state)
    foreignWithin : InInterval (foreignBounds box) (foreignDiscount state)
open InBox public

-- Signed foreign notional is held fixed. The inequalities below use q≥0;
-- reversing that contract is handled explicitly by negating its bounds.
lowerValue upperValue : FXSwap → FXBox → ℝ
lowerValue swap box = signedForeign swap ·ᵣ
  (lo (spotBounds box) ·ᵣ lo (foreignBounds box)
    -ᵣ farRate swap ·ᵣ hi (domesticBounds box))
upperValue swap box = signedForeign swap ·ᵣ
  (hi (spotBounds box) ·ᵣ hi (foreignBounds box)
    -ᵣ farRate swap ·ᵣ lo (domesticBounds box))

far-value-lower : ∀ swap box state → 0 ≤ᵣ signedForeign swap → InBox box state →
  lowerValue swap box ≤ᵣ farValue swap state
far-value-lower swap box state q₊ member = isTrans≤≡ᵣ _ _ _
  (≤ᵣ-o·ᵣ _ _ (signedForeign swap) q₊
    (≤ᵣMonotone+ᵣ _ _ _ _
      (product-lower (spotBounds box) (foreignBounds box) (spot state) (foreignDiscount state)
        (spotWithin member) (foreignWithin member))
      (-ᵣ≤ᵣ _ _
        (≤ᵣ-o·ᵣ _ _ (farRate swap) (<ᵣWeaken≤ᵣ _ _ (far-positive swap))
          (belowHi (domesticWithin member))))))
  (sym (far-value-formula swap state))

far-value-upper : ∀ swap box state → 0 ≤ᵣ signedForeign swap → InBox box state →
  farValue swap state ≤ᵣ upperValue swap box
far-value-upper swap box state q₊ member = isTrans≡≤ᵣ _ _ _
  (far-value-formula swap state)
  (≤ᵣ-o·ᵣ _ _ (signedForeign swap) q₊
    (≤ᵣMonotone+ᵣ _ _ _ _
      (product-upper (spotBounds box) (foreignBounds box) (spot state) (foreignDiscount state)
        (spotWithin member) (foreignWithin member))
      (-ᵣ≤ᵣ _ _
        (≤ᵣ-o·ᵣ _ _ (farRate swap) (<ᵣWeaken≤ᵣ _ _ (far-positive swap))
          (aboveLo (domesticWithin member))))))

-- These bounds quantify over every real state in the box, including joint
-- moves of spot and both effective discount factors. They do not depend
-- on enumerating test scenarios or discarding the spot/funding interaction.
far-value-bounds : ∀ swap box state → 0 ≤ᵣ signedForeign swap → InBox box state →
  (lowerValue swap box ≤ᵣ farValue swap state) × (farValue swap state ≤ᵣ upperValue swap box)
far-value-bounds swap box state q₊ member =
  far-value-lower swap box state q₊ member , far-value-upper swap box state q₊ member

reversed-value-bounds : ∀ swap box state → 0 ≤ᵣ signedForeign swap → InBox box state →
  ((-ᵣ upperValue swap box) ≤ᵣ farValue (reverseSwap swap) state) ×
  (farValue (reverseSwap swap) state ≤ᵣ -ᵣ lowerValue swap box)
reversed-value-bounds swap box state q₊ member =
  isTrans≤≡ᵣ _ _ _ (-ᵣ≤ᵣ _ _ (far-value-upper swap box state q₊ member))
    (sym (reverse-value swap state)) ,
  isTrans≡≤ᵣ _ _ _ (reverse-value swap state)
    (-ᵣ≤ᵣ _ _ (far-value-lower swap box state q₊ member))
