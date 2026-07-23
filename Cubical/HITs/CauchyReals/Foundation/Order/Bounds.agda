module Cubical.HITs.CauchyReals.Foundation.Order.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (pos)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Density public using
  (<ᵣ→Δ)
open import Cubical.HITs.CauchyReals.Foundation.Order.RationalBounds public
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base using
  (-ᵣ≤ᵣ; -ᵣ<ᵣ)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Strict using
  (≤absᵣ)
open import Cubical.HITs.CauchyReals.Algebra.Order.Lattice using
  (max<-lem)
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue using
  (abs-max)
open import Cubical.HITs.CauchyReals.Algebra.Order.Archimedean public using
  (∃ℚ₊LargerThanℝ₊; ∃ℚ₊LargerThanℝ₀₊)

ointerval→abs< : ∀ x y → x ∈ ointervalℙ (-ᵣ y) y → absᵣ x <ᵣ y
ointerval→abs< x y (-y<x , x<y) =
  isTrans≡<ᵣ _ _ _ (abs-max x)
    (max<-lem x (-ᵣ x) y x<y
      (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ _ _ -y<x) (-ᵣInvol y)))

abs<→ointerval : ∀ x y → absᵣ x <ᵣ y → x ∈ ointervalℙ (-ᵣ y) y
abs<→ointerval x y ∣x∣<y =
  isTrans<≡ᵣ _ _ _
    (-ᵣ<ᵣ _ _
      (isTrans≤<ᵣ _ _ _
        (isTrans≤≡ᵣ _ _ _ (≤absᵣ (-ᵣ x)) (sym (-absᵣ x)))
        ∣x∣<y))
    (-ᵣInvol x)
  , isTrans≤<ᵣ _ _ _ (≤absᵣ x) ∣x∣<y

abs≤→interval : ∀ x y → absᵣ x ≤ᵣ y → x ∈ intervalℙ (-ᵣ y) y
abs≤→interval x y ∣x∣≤y =
  isTrans≤≡ᵣ _ _ _
    (-ᵣ≤ᵣ _ _
      (isTrans≤ᵣ _ _ _
        (isTrans≤≡ᵣ _ _ _ (≤absᵣ (-ᵣ x)) (sym (-absᵣ x)))
        ∣x∣≤y))
    (-ᵣInvol x)
  , isTrans≤ᵣ _ _ _ (≤absᵣ x) ∣x∣≤y


-- Previous name: lowBnd-1/ℕ.
∃UnitFractionBelowℝ₊ : ∀ (x : ℝ₊) →
  ∃[ k ∈ ℕ₊₁ ] rat [ pos 1 / k ] <ᵣ fst x
∃UnitFractionBelowℝ₊ x = PT.map
  (λ (q , 0<q , q<x) →
    let q₊ : ℚ₊
        q₊ = q , <ᵣ→<ℚ 0 q 0<q
        k , 1/k<q = ℚ.lowerBoundℕ⁻¹ q₊
    in k , isTrans<ᵣ _ _ _ (<ℚ→<ᵣ [ pos 1 / k ] q 1/k<q) q<x)
  (denseℚinℝ 0 (fst x) (snd x))
