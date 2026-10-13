module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.InterpolationClocks where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.FiniteStitching
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

private
  cancel-offset : (a : ℚ) → (a ℚ.- 1) ℚ.+ (1 ℚ.- a) ≡ 0
  cancel-offset a = ℚ!
  end-offset : (a : ℚ) → a ℚ.+ (1 ℚ.- a) ≡ 1
  end-offset a = ℚ!
  step-offset : (a : ℚ) → a ℚ.+ 1 ≡ (a ℚ.+ 2) ℚ.- 1
  step-offset a = ℚ!
  return-offset : (a b : ℚ) → (a ℚ.- b) ℚ.+ b ≡ a
  return-offset a b = ℚ!
  affine-one : (a b : ℝ) → 1 ·ᵣ a +ᵣ b ≡ a +ᵣ b
  affine-one a b = ℝ!
  width-form : (a : ℚ) → (a ℚ.+ [ 1 / 2 ]) ℚ.- (ℚ.- [ 3 / 2 ]) ≡ a ℚ.+ 2
  width-form a = ℚ!

-- Branch j moves between its samples on (2j-1,2j), and is constant
-- on the positive-width overlaps used by FiniteStitching.
clockUC : ℕ → UC[ ℝPremetricSpace , Interval ]
clockUC j = clipUC ∘UC translateUC (rat (1 ℚ.- cut j))

clock : ℕ → ℝ → 𝕀
clock j = fst (clockUC j)

clock-left : (j : ℕ) (z : ℝ) → z ≤ᵣ rat (cut j ℚ.- 1) → clock j z ≡ 𝟘
clock-left j z below = clip-below _
  (isTrans≤≡ᵣ _ _ _ (≤ᵣ-+o z (rat (cut j ℚ.- 1)) (rat (1 ℚ.- cut j)) below)
    (+ᵣ-rat _ _ ∙ cong rat (cancel-offset (cut j))))

clock-right : (j : ℕ) (z : ℝ) → rat (cut j) ≤ᵣ z → clock j z ≡ 𝟙
clock-right j z above = clip-above _
  (isTrans≡≤ᵣ _ _ _ (sym (+ᵣ-rat _ _ ∙ cong rat (end-offset (cut j))))
    (≤ᵣ-+o (rat (cut j)) z (rat (1 ℚ.- cut j)) above))

next-clock-left : (j : ℕ) (z : ℝ) → z <ᵣ rat (upper j) → clock (suc j) z ≡ 𝟘
next-clock-left j z below = clock-left (suc j) z
  (isTrans≤≡ᵣ _ _ _ (<ᵣWeaken≤ᵣ z _ below) (cong rat (step-offset (cut j))))

cut-nonnegative : (j : ℕ) → 0 ℚ.≤ cut j
cut-nonnegative zero = <≤ℚ!
cut-nonnegative (suc j) = ℚ.isTrans≤ _ _ _ (cut-nonnegative j) <≤ℚ!

start : ℚ
start = ℚ.- [ 3 / 2 ]

finish : ℕ → ℚ
finish j = cut j ℚ.+ [ 1 / 2 ]

start-before : (j : ℕ) → rat start <ᵣ rat (upper j)
start-before j = <ℚ→<ᵣ start (upper j)
  (ℚ.isTrans<≤ start (0 ℚ.+ 1) (upper j) <≤ℚ!
    (ℚ.≤-+o 0 (cut j) 1 (cut-nonnegative j)))

clock-at-start : clock zero (rat start) ≡ 𝟘
clock-at-start = clock-left zero (rat start) decℚ≤ᵣ?

clock-at-finish : (j : ℕ) → clock j (rat (finish j)) ≡ 𝟙
clock-at-finish j = clock-right j (rat (finish j)) (≤ℚ→≤ᵣ (cut j) (finish j) <≤ℚ!)

stretchUC : ℕ → UC[ Interval , ℝPremetricSpace ]
stretchUC j = affineUC (rat (finish j ℚ.- start)) (rat start) ∘UC coordinateUC

stretch-start : (j : ℕ) → fst (stretchUC j) 𝟘 ≡ rat start
stretch-start j = ℝ!

stretch-finish : (j : ℕ) → fst (stretchUC j) 𝟙 ≡ rat (finish j)
stretch-finish j = affine-one _ _ ∙ +ᵣ-rat (finish j ℚ.- start) start ∙
  cong rat (return-offset (finish j) start)

width-nonnegative : (j : ℕ) → 0 ℚ.≤ finish j ℚ.- start
width-nonnegative j = subst (0 ℚ.≤_) (sym (width-form (cut j)))
  (ℚ.isTrans≤ 0 (cut j) (cut j ℚ.+ 2) (cut-nonnegative j) <≤ℚ!)

stretch-upper : (j : ℕ) (t : 𝕀) → fst (stretchUC j) t ≤ᵣ rat (finish j)
stretch-upper j t = isTrans≤≡ᵣ _ (1 ·ᵣ rat (finish j ℚ.- start) +ᵣ rat start) _
  (≤ᵣ-+o (fst t ·ᵣ rat (finish j ℚ.- start)) (1 ·ᵣ rat (finish j ℚ.- start)) (rat start)
    (≤ᵣ-·o (fst t) 1 (finish j ℚ.- start) (width-nonnegative j) (snd (snd t))))
  (stretch-finish j)

stretch-before : (j : ℕ) (t : 𝕀) → fst (stretchUC j) t <ᵣ rat (upper j)
stretch-before j t = isTrans≤<ᵣ _ (rat (finish j)) (rat (upper j)) (stretch-upper j t)
  (<ℚ→<ᵣ (finish j) (upper j) <≤ℚ!)

stretch-lower : (j : ℕ) (t : 𝕀) → rat start ≤ᵣ fst (stretchUC j) t
stretch-lower j t = isTrans≡≤ᵣ (rat start) (0 ·ᵣ rat (finish j ℚ.- start) +ᵣ rat start) _
  (sym (stretch-start j))
  (≤ᵣ-+o (0 ·ᵣ rat (finish j ℚ.- start)) (fst t ·ᵣ rat (finish j ℚ.- start)) (rat start)
    (≤ᵣ-·o 0 (fst t) (finish j ℚ.- start) (width-nonnegative j) (fst (snd t))))
