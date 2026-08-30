module Cubical.Analysis.Real.Sequence.Asymptotic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
  using (ℕ)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚInstance

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually

open ℚInstance.PositiveRationals
  using (ℚ₊; _+₊_; ℚ₊≡)
open ℚInstance.PositiveRationals.PositiveHalvesℚ
  using (_/2₊)


private
  substCloseness : ∀ x y {ε δ} →
    fst ε ≡ fst δ → x ∼[ ε ] y → x ∼[ δ ] y
  substCloseness x y equal =
    subst (x ∼[_] y) (ℚ₊≡ equal)


AsymptoticallyCloseTail :
  (x y : ℕ → ℝ) → ℚ₊ → Type₀
AsymptoticallyCloseTail x y ε =
  Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → x n ∼[ ε ] y n)


-- The cutoff is merely available at each radius.  This is intentionally
-- weaker than choosing a single modulus function for all radii.
AsymptoticallyCloseSequence :
  (ℕ → ℝ) → (ℕ → ℝ) → Type₀
AsymptoticallyCloseSequence x y =
  ∀ ε → ∥ AsymptoticallyCloseTail x y ε ∥₁


isPropAsymptoticallyCloseSequence : ∀ x y →
  isProp (AsymptoticallyCloseSequence x y)
isPropAsymptoticallyCloseSequence x y =
  isPropΠ λ _ → squash₁


asymptoticallyCloseRefl : ∀ x →
  AsymptoticallyCloseSequence x x
asymptoticallyCloseRefl x ε =
  ∣ 0 , (λ _ _ → refl∼ _ ε) ∣₁


asymptoticallyCloseSym : ∀ {x y} →
  AsymptoticallyCloseSequence x y →
  AsymptoticallyCloseSequence y x
asymptoticallyCloseSym {x} {y} close ε =
  PT.map
    (λ (N , eventually-close) →
      N , λ n N≤n →
        sym∼ (x n) (y n) ε (eventually-close n N≤n))
    (close ε)


asymptoticallyCloseTrans : ∀ {x y z} →
  AsymptoticallyCloseSequence x y →
  AsymptoticallyCloseSequence y z →
  AsymptoticallyCloseSequence x z
asymptoticallyCloseTrans {x} {y} {z} x∼y y∼z ε =
  PT.map2 combine (x∼y (ε /2₊)) (y∼z (ε /2₊))
  where
  combine :
    AsymptoticallyCloseTail x y (ε /2₊) →
    AsymptoticallyCloseTail y z (ε /2₊) →
    AsymptoticallyCloseTail x z ε
  combine (K , x-close-y) (L , y-close-z) =
    K +ℕ L , λ n sum≤n →
      substCloseness (x n) (z n)
        {ε = (ε /2₊) +₊ (ε /2₊)}
        {δ = ε}
        (ℚInstance.1/2∈ℚ./2+/2≡id (fst ε))
        (triangle∼ (x n) (y n) (z n)
          (ε /2₊) (ε /2₊)
          (x-close-y n
            (ℕ.≤-trans ℕ.≤SumLeft sum≤n))
          (y-close-z n
            (ℕ.≤-trans ℕ.≤SumRight sum≤n)))


eventuallyEqualTail→asymptoticallyClose : ∀ {x y} →
  EventuallyEqualTail x y →
  AsymptoticallyCloseSequence x y
eventuallyEqualTail→asymptoticallyClose {x} {y} (N , equal) ε =
  ∣ N , (λ n N≤n →
      subst (x n ∼[ ε ]_) (equal n N≤n) (refl∼ (x n) ε)) ∣₁


eventuallyEqual→asymptoticallyClose : ∀ {x y} →
  EventuallyEqualSequence x y →
  AsymptoticallyCloseSequence x y
eventuallyEqual→asymptoticallyClose {x} {y} eventually ε =
  PT.rec squash₁
    (λ tail →
      eventuallyEqualTail→asymptoticallyClose
        {x = x} {y = y} tail ε)
    eventually


asymptoticallyClosePresIsLimitSequence : ∀ {x y l} →
  AsymptoticallyCloseSequence x y →
  isLimitSequence x l →
  isLimitSequence y l
asymptoticallyClosePresIsLimitSequence {x} {y} {l}
    close x→l ε =
  PT.map2 combine (close (ε /2₊)) (x→l (ε /2₊))
  where
  combine :
    AsymptoticallyCloseTail x y (ε /2₊) →
    (Σ[ N ∈ ℕ ]
      (∀ n → N ℕ.≤ n → x n ∼[ ε /2₊ ] l)) →
    Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → y n ∼[ ε ] l)
  combine (K , x-close-y) (L , x-close-l) =
    K +ℕ L , λ n sum≤n →
      substCloseness (y n) l
        {ε = (ε /2₊) +₊ (ε /2₊)}
        {δ = ε}
        (ℚInstance.1/2∈ℚ./2+/2≡id (fst ε))
        (triangle∼ (y n) (x n) l
          (ε /2₊) (ε /2₊)
          (sym∼ (x n) (y n) (ε /2₊)
            (x-close-y n
              (ℕ.≤-trans ℕ.≤SumLeft sum≤n)))
          (x-close-l n
            (ℕ.≤-trans ℕ.≤SumRight sum≤n)))


asymptoticallyCloseReflectsIsLimitSequence : ∀ {x y l} →
  AsymptoticallyCloseSequence x y →
  isLimitSequence y l →
  isLimitSequence x l
asymptoticallyCloseReflectsIsLimitSequence {x} {y} close =
  asymptoticallyClosePresIsLimitSequence
    (asymptoticallyCloseSym {x = x} {y = y} close)
