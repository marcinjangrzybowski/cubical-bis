module Cubical.Analysis.Real.Sequence.SelectedAsymptotic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚInstance

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Asymptotic

open ℚInstance.PositiveRationals
  using (ℚ₊; _+₊_; ℚ₊≡)
open ℚInstance.PositiveRationals.PositiveHalvesℚ
  using (_/2₊; _/4₊)


-- A selected asymptotic modulus is stronger than the radiuswise truncated
-- relation.  Keeping this distinction explicit is what lets it preserve the
-- completion constructor's selected global Cauchy modulus without choice.
ChosenAsymptoticallyCloseSequence :
  (ℕ → ℝ) → (ℕ → ℝ) → Type₀
ChosenAsymptoticallyCloseSequence x y =
  ∀ ε → AsymptoticallyCloseTail x y ε


SelectedAsymptoticallyCloseSequence :
  (ℕ → ℝ) → (ℕ → ℝ) → Type₀
SelectedAsymptoticallyCloseSequence x y =
  ∥ ChosenAsymptoticallyCloseSequence x y ∥₁


isPropSelectedAsymptoticallyCloseSequence : ∀ x y →
  isProp (SelectedAsymptoticallyCloseSequence x y)
isPropSelectedAsymptoticallyCloseSequence x y = squash₁


selectedAsymptotic→asymptotic : ∀ {x y} →
  SelectedAsymptoticallyCloseSequence x y →
  AsymptoticallyCloseSequence x y
selectedAsymptotic→asymptotic {x} {y} =
  PT.rec (isPropAsymptoticallyCloseSequence x y)
    (λ selected ε → ∣ selected ε ∣₁)


selectedAsymptoticallyCloseRefl : ∀ x →
  SelectedAsymptoticallyCloseSequence x x
selectedAsymptoticallyCloseRefl x =
  ∣ (λ ε → 0 , (λ _ _ → refl∼ _ ε)) ∣₁


selectedAsymptoticallyCloseSym : ∀ {x y} →
  SelectedAsymptoticallyCloseSequence x y →
  SelectedAsymptoticallyCloseSequence y x
selectedAsymptoticallyCloseSym {x} {y} =
  PT.map λ selected ε →
    let N , close = selected ε
    in N , λ n N≤n →
      sym∼ (x n) (y n) ε (close n N≤n)


private
  quarterHalfQuarter : ∀ ε →
    fst ((ε /4₊) +₊ ((ε /2₊) +₊ (ε /4₊))) ≡ fst ε
  quarterHalfQuarter ε =
    ℚ.+Assoc
      (fst (ε /4₊)) (fst (ε /2₊)) (fst (ε /4₊))
    ∙ cong (ℚ._+ fst (ε /4₊))
        (ℚ.+Comm (fst (ε /4₊)) (fst (ε /2₊)))
    ∙ sym (ℚ.+Assoc
        (fst (ε /2₊)) (fst (ε /4₊)) (fst (ε /4₊)))
    ∙ cong (fst (ε /2₊) ℚ.+_)
        (ℚInstance.1/2∈ℚ./4+/4≡/2 (fst ε))
    ∙ ℚInstance.1/2∈ℚ./2+/2≡id (fst ε)

  substCloseness : ∀ x y {ε δ} →
    fst ε ≡ fst δ → x ∼[ ε ] y → x ∼[ δ ] y
  substCloseness x y equal =
    subst (x ∼[_] y) (ℚ₊≡ equal)


selectedAsymptoticallyCloseTrans : ∀ {x y z} →
  SelectedAsymptoticallyCloseSequence x y →
  SelectedAsymptoticallyCloseSequence y z →
  SelectedAsymptoticallyCloseSequence x z
selectedAsymptoticallyCloseTrans {x} {y} {z} =
  PT.map2 combine
  where
  combine :
    ChosenAsymptoticallyCloseSequence x y →
    ChosenAsymptoticallyCloseSequence y z →
    ChosenAsymptoticallyCloseSequence x z
  combine x∼y y∼z ε =
    let
      K , left = x∼y (ε /2₊)
      L , right = y∼z (ε /2₊)
    in
    ℕ.max K L , λ n max≤n →
      substCloseness (x n) (z n)
        (ℚInstance.1/2∈ℚ./2+/2≡id (fst ε))
        (triangle∼ (x n) (y n) (z n)
          (ε /2₊) (ε /2₊)
          (left n
            (ℕ.≤-trans
              (ℕ.left-≤-max {m = K} {n = L}) max≤n))
          (right n
            (ℕ.≤-trans
              (ℕ.right-≤-max {n = L} {m = K}) max≤n)))


selectedAsymptoticPresSeqWitness : ∀ {x y} →
  SelectedAsymptoticallyCloseSequence x y →
  SeqWitness x → SeqWitness y
selectedAsymptoticPresSeqWitness {x} {y} =
  PT.map2 combine
  where
  combine :
    ChosenAsymptoticallyCloseSequence x y →
    ChosenIsCauchySequence x →
    ChosenIsCauchySequence y
  combine selected x-cauchy .fst ε =
    ℕ.max (fst (selected (ε /4₊)))
      (fst x-cauchy (ε /2₊))
  combine selected x-cauchy .snd ε m n max≤m max≤n =
    substCloseness (y m) (y n)
      (quarterHalfQuarter ε)
      (triangle∼
        (y m) (x m) (y n)
        (ε /4₊) ((ε /2₊) +₊ (ε /4₊))
        (sym∼ (x m) (y m) (ε /4₊)
          (snd (selected (ε /4₊)) m
            (ℕ.≤-trans
              (ℕ.left-≤-max
                {m = fst (selected (ε /4₊))}
                {n = fst x-cauchy (ε /2₊)})
              max≤m)))
        (triangle∼
          (x m) (x n) (y n)
          (ε /2₊) (ε /4₊)
          (snd x-cauchy (ε /2₊) m n
            (ℕ.≤-trans
              (ℕ.right-≤-max
                {n = fst x-cauchy (ε /2₊)}
                {m = fst (selected (ε /4₊))})
              max≤m)
            (ℕ.≤-trans
              (ℕ.right-≤-max
                {n = fst x-cauchy (ε /2₊)}
                {m = fst (selected (ε /4₊))})
              max≤n))
          (snd (selected (ε /4₊)) n
            (ℕ.≤-trans
              (ℕ.left-≤-max
                {m = fst (selected (ε /4₊))}
                {n = fst x-cauchy (ε /2₊)})
              max≤n))))


selectedAsymptoticReflectsSeqWitness : ∀ {x y} →
  SelectedAsymptoticallyCloseSequence x y →
  SeqWitness y → SeqWitness x
selectedAsymptoticReflectsSeqWitness {x} {y} selected =
  selectedAsymptoticPresSeqWitness
    (selectedAsymptoticallyCloseSym {x = x} {y = y} selected)
