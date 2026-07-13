module Cubical.HITs.CauchyReals.OrderBounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (pos)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.RationalsImports

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

∃ℚ₊LargerThanℝ₊ : ∀ (x : ℝ₊) → ∃[ q ∈ ℚ₊ ] fst x <ᵣ rat (fst q)
∃ℚ₊LargerThanℝ₊ x = PT.map
  (λ (q , x<q , _) →
     (q ,  (<ᵣ→<ℚ 0 q (isTrans<ᵣ _ _ _ (snd x) x<q))) , x<q)
   (denseℚinℝ (fst x) (fst x +ᵣ 1)
     (isTrans≡<ᵣ _ _ _
        (sym (+IdR (fst x)))
        (<ᵣ-o+ _ _ (fst x) (decℚ<ᵣ? {0} {1}))))

∃ℚ₊LargerThanℝ₀₊ : ∀ (x : ℝ₀₊) → ∃[ q ∈ ℚ₊ ] fst x <ᵣ rat (fst q)
∃ℚ₊LargerThanℝ₀₊ x = PT.map
  (λ (q , x<q , _) →
     (q ,  (<ᵣ→<ℚ 0 q (isTrans≤<ᵣ _ _ _ (snd x) x<q))) , x<q)
   (denseℚinℝ (fst x) (fst x +ᵣ 1)
     (isTrans≡<ᵣ _ _ _
        (sym (+IdR (fst x)))
        (<ᵣ-o+ _ _ (fst x) (decℚ<ᵣ? {0} {1}))))

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
