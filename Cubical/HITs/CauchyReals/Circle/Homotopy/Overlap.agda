module Cubical.HITs.CauchyReals.Circle.Homotopy.Overlap where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (ℤ; pos; negsuc)
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Algebra.Ring using (module Rℝ)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Algebra.Order.Lattice
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Equivalence
open import Cubical.HITs.CauchyReals.Circle.UniformGroup
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

opaque
  overlapCircleEquivalence : (ε : ℝ₊) → CircleOverlap[ ε ] ≃ Circle
  overlapCircleEquivalence ε = CircleOverlap≃distCircle ε ∙ₑ invEquiv cartesianEquivalence

  overlapCircle-β : (ε : ℝ₊) (r : ℝ) (inside : r ∈ ointervalℙ 0 (1 +ᵣ fst ε)) →
    equivFun (overlapCircleEquivalence ε) SQ.[ (r , inside) ] ≡ injCircle r
  overlapCircle-β ε r inside = cong (invEq cartesianEquivalence)
    (sym (cartesianEquivalence-β (injCircle r))) ∙ retEq cartesianEquivalence (injCircle r)

overlapRepresentative : (ε : ℝ₊) (p : Circle) →
  ∥ Σ[ r ∈ ℝ ] (r ∈ ointervalℙ 0 (1 +ᵣ fst ε)) × (injCircle r ≡ p) ∥₁
overlapRepresentative ε p = subst
  (λ z → ∥ Σ[ r ∈ ℝ ] (r ∈ ointervalℙ 0 (1 +ᵣ fst ε)) × (injCircle r ≡ z) ∥₁)
  (secEq (overlapCircleEquivalence ε) p)
  (represent (invEq (overlapCircleEquivalence ε) p))
  where
  represent : (z : CircleOverlap[ ε ]) →
    ∥ Σ[ r ∈ ℝ ] (r ∈ ointervalℙ 0 (1 +ᵣ fst ε)) ×
      (injCircle r ≡ equivFun (overlapCircleEquivalence ε) z) ∥₁
  represent = SQ.elimProp (λ _ → squash₁)
    (λ (r , inside) → ∣ r , inside , sym (overlapCircle-β ε r inside) ∣₁)

-- Representatives with a fixed margin inside (0, 3/2). Locatedness
-- supplies the finite alternative; it does not decide a real cut.
innerRepresentative : (p : Circle) →
  ∥ Σ[ r ∈ ℝ ] ((rat [ 1 / 8 ] <ᵣ r) × (r <ᵣ rat [ 5 / 4 ])) × (injCircle r ≡ p) ∥₁
innerRepresentative p = PT.rec squash₁ choose (overlapRepresentative (ℚ₊→ℝ₊ ([ 1 / 4 ]₊)) p)
  where
  choose : (Σ[ r ∈ ℝ ] (r ∈ ointervalℙ 0 (1 +ᵣ rat [ 1 / 4 ])) × (injCircle r ≡ p)) →
    ∥ Σ[ r ∈ ℝ ] ((rat [ 1 / 8 ] <ᵣ r) × (r <ᵣ rat [ 5 / 4 ])) × (injCircle r ≡ p) ∥₁
  choose (r , (positive , upper) , represents) = PT.map cases
    (isWeaklyLinear<ᵣ (rat [ 1 / 8 ]) (rat [ 1 / 4 ]) r decℚ<ᵣ?)
    where
    cases : ((rat [ 1 / 8 ] <ᵣ r) ⊎ (r <ᵣ rat [ 1 / 4 ])) →
      Σ[ s ∈ ℝ ] ((rat [ 1 / 8 ] <ᵣ s) × (s <ᵣ rat [ 5 / 4 ])) × (injCircle s ≡ p)
    cases (inl lower) = r , (lower , isTrans<≡ᵣ _ _ _ upper (+ᵣ-rat 1 [ 1 / 4 ])) , represents
    cases (inr upper) = (r +ᵣ 1) ,
      (isTrans<ᵣ _ 1 _ decℚ<ᵣ? (isTrans≡<ᵣ _ _ _ (sym (+IdL 1)) (<ᵣ-+o 0 r 1 positive)) ,
        isTrans<≡ᵣ _ _ _ (<ᵣ-+o r (rat [ 1 / 4 ]) 1 upper) (+ᵣ-rat [ 1 / 4 ] 1)) ,
      SQ.eq/ _ _ (1 , ℝ!) ∙ represents

private
  smallInteger : (k : ℤ) → -2 ℤ.< k → k ℤ.< 2 →
    (k ≡ 0) ⊎ ((k ≡ 1) ⊎ (k ≡ -1))
  smallInteger (pos zero) lower upper = inl refl
  smallInteger (pos (suc zero)) lower upper = inr (inl refl)
  smallInteger (pos (suc (suc n))) lower (ℤ.pos<pos ())
  smallInteger (negsuc zero) lower upper = inr (inr refl)
  smallInteger (negsuc (suc n)) (ℤ.negsuc<negsuc ()) upper

  integerLess : ∀ m n → rat [ m / 1 ] <ᵣ rat [ n / 1 ] → m ℤ.< n
  integerLess m n less = subst2 ℤ._<_ (ℤ.·IdR m) (ℤ.·IdR n)
    (ℚ._<_.prf (<ᵣ→<ℚ [ m / 1 ] [ n / 1 ] less))

  difference-upper : ∀ x y → x <ᵣ rat [ 3 / 2 ] → 0 <ᵣ y → x -ᵣ y <ᵣ 2
  difference-upper x y x-upper y-positive = isTrans<ᵣ _ (rat [ 3 / 2 ]) 2
    (isTrans<≡ᵣ _ _ _
      (<ᵣMonotone+ᵣ x (rat [ 3 / 2 ]) (-ᵣ y) 0 x-upper
        (isTrans<≡ᵣ _ _ _ (-ᵣ<ᵣ 0 y y-positive) (-ᵣ-rat 0))) (+IdR _)) decℚ<ᵣ?

-- On an overlap of width 3/2 only the integers -1, 0, and 1 occur.
overlap-respects : (h : ℝ → ℝ) →
  (∀ t → -1 ≤ᵣ t → t ≤ᵣ 1 → h (t +ᵣ 1) ≡ h t) →
  ∀ x y → 0 <ᵣ x → x <ᵣ rat [ 3 / 2 ] → 0 <ᵣ y → y <ᵣ rat [ 3 / 2 ] →
  circle-rel x y → h x ≡ h y
overlap-respects h periodic x y xlo xhi ylo yhi (k , difference) = cases
  (smallInteger k
    (integerLess -2 k (isTrans<≡ᵣ _ _ _
      (subst2 _<ᵣ_ (-ᵣ-rat 2) ℝ! (-ᵣ<ᵣ (y -ᵣ x) 2 (difference-upper y x yhi xlo))) difference))
    (integerLess k 2 (isTrans≡<ᵣ _ _ _ (sym difference) (difference-upper x y xhi ylo))))
  where
  one-step : ∀ a b → a <ᵣ rat [ 3 / 2 ] → 0 <ᵣ b → a -ᵣ b ≡ 1 → h a ≡ h b
  one-step a b ahi blo diff = cong h shift ∙ periodic b
    (<ᵣWeaken≤ᵣ _ _ (isTrans<ᵣ -1 0 b decℚ<ᵣ? blo)) (<ᵣWeaken≤ᵣ _ _ b<1)
    where
    shift : a ≡ b +ᵣ 1
    shift = sym (Rℝ.minusPlus a b) ∙ cong (_+ᵣ b) diff ∙ +ᵣComm 1 b
    b<1 : b <ᵣ 1
    b<1 = subst2 _<ᵣ_ ℝ! ℝ! (<ᵣ-+o (b +ᵣ 1) 2 (-ᵣ 1)
      (subst (_<ᵣ 2) shift (isTrans<ᵣ a (rat [ 3 / 2 ]) 2 ahi decℚ<ᵣ?)))
  cases : (k ≡ 0) ⊎ ((k ≡ 1) ⊎ (k ≡ -1)) → h x ≡ h y
  cases (inl k0) = cong h (Rℝ.equalByDifference x y (difference ∙ cong (λ k → rat [ k / 1 ]) k0))
  cases (inr (inl k1)) = one-step x y xhi ylo (difference ∙ cong (λ k → rat [ k / 1 ]) k1)
  cases (inr (inr k-1)) = sym (one-step y x yhi xlo
    (sym (-[x-y]≡y-x x y) ∙ cong -ᵣ_ (difference ∙ cong (λ k → rat [ k / 1 ]) k-1)
      ∙ -ᵣ-rat -1))
