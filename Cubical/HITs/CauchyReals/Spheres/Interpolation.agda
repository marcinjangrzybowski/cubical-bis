module Cubical.HITs.CauchyReals.Spheres.Interpolation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.Sigma
import Cubical.Algebra.OrderedCommRing.Properties as Ordered
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance using (ℝOrderedCommRing)
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive using (nonNegativeMulClosed)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval using (𝕀; 𝟘; 𝟙; reverseTime)
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.Coordinates
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

private
  module Order = Ordered.OrderedCommRingTheory ℝOrderedCommRing

  half : ℝ
  half = rat [ 1 / 2 ]

  weight-squares-bound : (t : ℝ) →
    half ≤ᵣ (1 -ᵣ t) ·ᵣ (1 -ᵣ t) +ᵣ t ·ᵣ t
  weight-squares-bound t = Order.0≤Δ→≤ _ _
    (isTrans≤≡ᵣ _ _ _
      (nonNegativeMulClosed 2 _ decℚ≤ᵣ? (Order.0≤² (t -ᵣ half))) ℝ!)

  cross-coefficient-nonnegative : (t : 𝕀) →
    0 ≤ᵣ 2 ·ᵣ (1 -ᵣ fst t) ·ᵣ fst t
  cross-coefficient-nonnegative t = nonNegativeMulClosed _ _
    (nonNegativeMulClosed _ _ decℚ≤ᵣ? (fst (snd (reverseTime t))))
    (fst (snd t))

-- This estimate works for every nonnegative dot product, including zero.
-- It supplies one denominator bound for all coordinate-cover contractions.
norm²-blend-lower-bound : (m : ℕ) (t : 𝕀) (x y : RealSphere m) →
  0 ≤ᵣ dot (suc m) (fst x) (fst y) →
  rat [ 1 / 2 ] ≤ᵣ norm² (suc m) (blend (suc m) (fst t) (fst x) (fst y))
norm²-blend-lower-bound m t x y nonnegative =
  isTrans≤≡ᵣ _ _ _
    (isTrans≤ᵣ _ _ _ (weight-squares-bound (fst t))
      (Order.≤SumLeftNonNeg _ _
        (nonNegativeMulClosed _ _ (cross-coefficient-nonnegative t) nonnegative)))
    (sym (norm²-blend-sphere m (fst t) x y))

norm²-blend-positive : (m : ℕ) (t : 𝕀) (x y : RealSphere m) →
  0 ≤ᵣ dot (suc m) (fst x) (fst y) →
  0 <ᵣ norm² (suc m) (blend (suc m) (fst t) (fst x) (fst y))
norm²-blend-positive m t x y nonnegative =
  isTrans<≤ᵣ _ _ _ decℚ<ᵣ? (norm²-blend-lower-bound m t x y nonnegative)

squaredDistance : (n : ℕ) → fst (Euclidean n) → fst (Euclidean n) → ℝ
squaredDistance n x y = norm² n (linearCombination n 1 x (-1) y)

squaredDistance-sphere : (m : ℕ) (x y : RealSphere m) →
  squaredDistance (suc m) (fst x) (fst y) ≡ 2 -ᵣ 2 ·ᵣ dot (suc m) (fst x) (fst y)
squaredDistance-sphere m x y = norm²-linearCombination (suc m) 1 (fst x) (-1) (fst y) ∙
  cong₂ (λ a b → 1 ·ᵣ 1 ·ᵣ a +ᵣ (-1) ·ᵣ (-1) ·ᵣ b +ᵣ
    (2 ·ᵣ 1 ·ᵣ (-1)) ·ᵣ dot (suc m) (fst x) (fst y)) (snd x) (snd y) ∙ ℝ!

-- A squared-distance bound suffices; no Euclidean triangle inequality or
-- Cauchy--Schwarz theorem is needed for this nonvanishing argument.
close-spheres-dot-nonnegative : (m : ℕ) (x y : RealSphere m) →
  squaredDistance (suc m) (fst x) (fst y) ≤ᵣ 2 →
  0 ≤ᵣ dot (suc m) (fst x) (fst y)
close-spheres-dot-nonnegative m x y close = isTrans≤≡ᵣ _ _ _
  (nonNegativeMulClosed half _ decℚ≤ᵣ? (Order.≤→0≤Δ _ _ close))
  (cong (λ a → half ·ᵣ (2 -ᵣ a)) (squaredDistance-sphere m x y) ∙ ℝ!)
