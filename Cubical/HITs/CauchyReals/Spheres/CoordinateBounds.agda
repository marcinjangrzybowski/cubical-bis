module Cubical.HITs.CauchyReals.Spheres.CoordinateBounds where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as Nat
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
import Cubical.Algebra.OrderedCommRing.Properties as Ordered
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance using (ℝOrderedCommRing)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition using (≤ᵣMonotone+ᵣ)
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication using (≤ᵣ-o·ᵣ)
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue using (absᵣNonNeg; absᵣ-triangle)
open import Cubical.HITs.CauchyReals.Algebra.Power.Base using (1^ⁿ; x·x≡∣x∣·∣x∣)
open import Cubical.HITs.CauchyReals.Algebra.Power.Order using (^ⁿ-reflects-≤)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval using (𝕀; reverseTime)
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.Coordinates
open import Cubical.HITs.CauchyReals.Spheres.UniformNormalization using (CoordinateBound)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

private
  module Order = Ordered.OrderedCommRingTheory ℝOrderedCommRing

  square-bound→abs-bound : (x : ℝ) → x ·ᵣ x ≤ᵣ 1 → absᵣ x ≤ᵣ 1
  square-bound→abs-bound x bound = ^ⁿ-reflects-≤ 2 (Nat.suc-≤-suc Nat.zero-≤)
    (0≤absᵣ x) decℚ≤ᵣ?
    (isTrans≡≤ᵣ _ _ _ (x^²=x·x _ ∙ sym (x·x≡∣x∣·∣x∣ x))
      (isTrans≤≡ᵣ _ _ _ bound (sym (1^ⁿ 2))))

  weighted-abs-bound : (a x : ℝ) → 0 ≤ᵣ a → absᵣ x ≤ᵣ 1 → absᵣ (a ·ᵣ x) ≤ᵣ a
  weighted-abs-bound a x nonnegative bound =
    isTrans≡≤ᵣ _ _ _ (·absᵣ a x ∙ cong (_·ᵣ absᵣ x) (absᵣNonNeg a nonnegative))
      (isTrans≤≡ᵣ _ _ _ (≤ᵣ-o·ᵣ _ _ a nonnegative bound) ℝ!)

  scalar-blend-bound : (t : 𝕀) (x y : ℝ) → absᵣ x ≤ᵣ 1 → absᵣ y ≤ᵣ 1 →
    absᵣ ((1 -ᵣ fst t) ·ᵣ x +ᵣ fst t ·ᵣ y) ≤ᵣ 1
  scalar-blend-bound t x y x-bound y-bound = isTrans≤ᵣ _ _ _ (absᵣ-triangle _ _)
    (isTrans≤≡ᵣ _ _ _
      (≤ᵣMonotone+ᵣ _ _ _ _
        (weighted-abs-bound _ x (fst (snd (reverseTime t))) x-bound)
        (weighted-abs-bound _ y (fst (snd t)) y-bound)) ℝ!)

unit-ball-coordinate-bound : (n : ℕ) (x : fst (Euclidean n)) →
  norm² n x ≤ᵣ 1 → CoordinateBound n 1 x
unit-ball-coordinate-bound zero x bound = tt
unit-ball-coordinate-bound (suc zero) x bound = square-bound→abs-bound x bound
unit-ball-coordinate-bound (suc (suc n)) (x , xs) bound =
  square-bound→abs-bound x
    (isTrans≤ᵣ _ _ _ (Order.≤SumLeftNonNeg _ _ (norm²-nonnegative (suc n) xs)) bound) ,
  unit-ball-coordinate-bound (suc n) xs
    (isTrans≤ᵣ _ _ _ (Order.≤SumRightNonNeg _ _ (Order.0≤² x)) bound)

sphere-coordinate-bound : (m : ℕ) (x : RealSphere m) → CoordinateBound (suc m) 1 (fst x)
sphere-coordinate-bound m x = unit-ball-coordinate-bound (suc m) (fst x)
  (≡ᵣWeaken≤ᵣ _ _ (snd x))

blend-coordinate-bound : (n : ℕ) (t : 𝕀) (x y : fst (Euclidean n)) →
  CoordinateBound n 1 x → CoordinateBound n 1 y → CoordinateBound n 1 (blend n (fst t) x y)
blend-coordinate-bound zero t x y x-bound y-bound = tt
blend-coordinate-bound (suc zero) t x y x-bound y-bound = scalar-blend-bound t x y x-bound y-bound
blend-coordinate-bound (suc (suc n)) t (x , xs) (y , ys) x-bound y-bound =
  scalar-blend-bound t x y (fst x-bound) (fst y-bound) ,
  blend-coordinate-bound (suc n) t xs ys (snd x-bound) (snd y-bound)
