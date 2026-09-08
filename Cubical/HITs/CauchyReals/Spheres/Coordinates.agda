module Cubical.HITs.CauchyReals.Spheres.Coordinates where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
import Cubical.Algebra.OrderedCommRing.Properties as Ordered
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance using (ℝOrderedCommRing)
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive using (nonNegativeAddClosed)
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

private
  module Order = Ordered.OrderedCommRingTheory ℝOrderedCommRing

-- Operations on the existing coordinate representation; no new metric.
scale : (n : ℕ) → ℝ → fst (Euclidean n) → fst (Euclidean n)
scale zero a x = tt
scale (suc zero) a x = a ·ᵣ x
scale (suc (suc n)) a (x , xs) = a ·ᵣ x , scale (suc n) a xs

linearCombination : (n : ℕ) → ℝ → fst (Euclidean n) →
  ℝ → fst (Euclidean n) → fst (Euclidean n)
linearCombination zero a x b y = tt
linearCombination (suc zero) a x b y = a ·ᵣ x +ᵣ b ·ᵣ y
linearCombination (suc (suc n)) a (x , xs) b (y , ys) =
  a ·ᵣ x +ᵣ b ·ᵣ y , linearCombination (suc n) a xs b ys

dot : (n : ℕ) → fst (Euclidean n) → fst (Euclidean n) → ℝ
dot zero x y = 0
dot (suc zero) x y = x ·ᵣ y
dot (suc (suc n)) (x , xs) (y , ys) = x ·ᵣ y +ᵣ dot (suc n) xs ys

scale-one : (n : ℕ) (x : fst (Euclidean n)) → scale n 1 x ≡ x
scale-one zero x = refl
scale-one (suc zero) x = ℝ!
scale-one (suc (suc n)) (x , xs) = cong₂ _,_ ℝ! (scale-one (suc n) xs)

dot-self : (n : ℕ) (x : fst (Euclidean n)) → dot n x x ≡ norm² n x
dot-self zero x = refl
dot-self (suc zero) x = refl
dot-self (suc (suc n)) (x , xs) = cong (x ·ᵣ x +ᵣ_) (dot-self (suc n) xs)

norm²-nonnegative : (n : ℕ) (x : fst (Euclidean n)) → 0 ≤ᵣ norm² n x
norm²-nonnegative zero x = ≤ᵣ-refl 0
norm²-nonnegative (suc zero) x = Order.0≤² x
norm²-nonnegative (suc (suc n)) (x , xs) =
  nonNegativeAddClosed _ _ (Order.0≤² x) (norm²-nonnegative (suc n) xs)

norm²-scale : (n : ℕ) (a : ℝ) (x : fst (Euclidean n)) →
  norm² n (scale n a x) ≡ (a ·ᵣ a) ·ᵣ norm² n x
norm²-scale zero a x = ℝ!
norm²-scale (suc zero) a x = ℝ!
norm²-scale (suc (suc n)) a (x , xs) =
  cong ((a ·ᵣ x) ·ᵣ (a ·ᵣ x) +ᵣ_) (norm²-scale (suc n) a xs) ∙ ℝ!

norm²-linearCombination : (n : ℕ) (a : ℝ) (x : fst (Euclidean n))
  (b : ℝ) (y : fst (Euclidean n)) →
  norm² n (linearCombination n a x b y) ≡
    (a ·ᵣ a) ·ᵣ norm² n x +ᵣ (b ·ᵣ b) ·ᵣ norm² n y +ᵣ
    (2 ·ᵣ a ·ᵣ b) ·ᵣ dot n x y
norm²-linearCombination zero a x b y = ℝ!
norm²-linearCombination (suc zero) a x b y = ℝ!
norm²-linearCombination (suc (suc n)) a (x , xs) b (y , ys) =
  cong ((a ·ᵣ x +ᵣ b ·ᵣ y) ·ᵣ (a ·ᵣ x +ᵣ b ·ᵣ y) +ᵣ_)
    (norm²-linearCombination (suc n) a xs b ys) ∙ ℝ!

blend : (n : ℕ) → ℝ → fst (Euclidean n) → fst (Euclidean n) → fst (Euclidean n)
blend n t x y = linearCombination n (1 -ᵣ t) x t y

blend-start : (n : ℕ) (x y : fst (Euclidean n)) → blend n 0 x y ≡ x
blend-start zero x y = refl
blend-start (suc zero) x y = ℝ!
blend-start (suc (suc n)) (x , xs) (y , ys) =
  cong₂ _,_ ℝ! (blend-start (suc n) xs ys)

blend-end : (n : ℕ) (x y : fst (Euclidean n)) → blend n 1 x y ≡ y
blend-end zero x y = refl
blend-end (suc zero) x y = ℝ!
blend-end (suc (suc n)) (x , xs) (y , ys) =
  cong₂ _,_ ℝ! (blend-end (suc n) xs ys)

blend-same : (n : ℕ) (t : ℝ) (x : fst (Euclidean n)) → blend n t x x ≡ x
blend-same zero t x = refl
blend-same (suc zero) t x = ℝ!
blend-same (suc (suc n)) t (x , xs) =
  cong₂ _,_ ℝ! (blend-same (suc n) t xs)

norm²-blend-sphere : (m : ℕ) (t : ℝ) (x y : RealSphere m) →
  norm² (suc m) (blend (suc m) t (fst x) (fst y)) ≡
    (1 -ᵣ t) ·ᵣ (1 -ᵣ t) +ᵣ t ·ᵣ t +ᵣ
    (2 ·ᵣ (1 -ᵣ t) ·ᵣ t) ·ᵣ dot (suc m) (fst x) (fst y)
norm²-blend-sphere m t x y =
  norm²-linearCombination (suc m) (1 -ᵣ t) (fst x) t (fst y) ∙
  cong₂ (λ a b → (1 -ᵣ t) ·ᵣ (1 -ᵣ t) ·ᵣ a +ᵣ t ·ᵣ t ·ᵣ b +ᵣ
    (2 ·ᵣ (1 -ᵣ t) ·ᵣ t) ·ᵣ dot (suc m) (fst x) (fst y)) (snd x) (snd y) ∙ ℝ!
