{-# OPTIONS --safe --cubical #-}

-- Robust constraints over an entire uncertainty set motivate these bounds:
-- ../../REFERENCES.md#ben-tal-nemirovski-1998 and #bis-fx-2016.
-- The +/-20% spot interval, discount factors [0.9,1] and principal 100 are
-- synthetic. Joint-factor bounds are proved for every real quote in the box.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.JointMoveExample where

open import Cubical.HITs.CauchyReals.Example.Financial.Instruments.FXBounds
open import Cubical.HITs.CauchyReals.Example.Financial.Instruments.FXSwap public
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

open import Cubical.HITs.CauchyReals.Foundation.Rationals using ([_/_])
open import Cubical.Data.NatPlusOne using (fromNatℕ₊₁)
open import Cubical.Data.Int.Base using (fromNatℤ)

-- Spot in [0.8,1.2]; both discount factors in [0.9,1].
jointBox : FXBox
jointBox = fx-box
  (bound (rat [ 4 / 5 ]) (rat [ 6 / 5 ]) decℚ≤ᵣ? decℚ≤ᵣ?)
  (bound (rat [ 9 / 10 ]) 1 decℚ≤ᵣ? decℚ≤ᵣ?)
  (bound (rat [ 9 / 10 ]) 1 decℚ≤ᵣ? decℚ≤ᵣ?)

lower-is-minus-twenty-eight : ∀ swap → signedForeign swap ≡ 100 → farRate swap ≡ 1 →
  lowerValue swap jointBox ≡ -28
lower-is-minus-twenty-eight swap notional rate = cong₂
  (λ q k → q ·ᵣ (lo (spotBounds jointBox) ·ᵣ lo (foreignBounds jointBox)
    -ᵣ k ·ᵣ hi (domesticBounds jointBox))) notional rate ∙ ℝ!

upper-is-thirty : ∀ swap → signedForeign swap ≡ 100 → farRate swap ≡ 1 →
  upperValue swap jointBox ≡ 30
upper-is-thirty swap notional rate = cong₂
  (λ q k → q ·ᵣ (hi (spotBounds jointBox) ·ᵣ hi (foreignBounds jointBox)
    -ᵣ k ·ᵣ lo (domesticBounds jointBox))) notional rate ∙ ℝ!
