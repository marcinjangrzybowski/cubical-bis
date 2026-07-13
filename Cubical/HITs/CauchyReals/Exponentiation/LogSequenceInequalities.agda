{-# OPTIONS --lossy-unification #-}

module Cubical.HITs.CauchyReals.Exponentiation.LogSequenceInequalities where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)
open import Cubical.Foundations.Function

open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using ([_/_])
open import Cubical.Data.Rationals.Inverse as ℚ⁻¹ using (_⁻¹₊)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

private
  ℚ₊fromSucNat : ∀ m → ℚ₊
  ℚ₊fromSucNat m = fromNat (suc m)

invℚ₊-fromNat : ∀ m → fst (ℚ⁻¹._⁻¹₊ (ℚ₊fromSucNat m)) ≡ [ pos 1 / 1+ m ]
invℚ₊-fromNat m =
  sym (ℚ.·IdL _) ∙
  cong₂ [_/_] (ℤ.·IdR (pos 1)) (·₊₁-identityˡ (1+ m))

private
  2ℝ₊ : ℝ₊
  2ℝ₊ = fromNat 2

  2₊ : ℚ₊
  2₊ = fromNat 2

open import Cubical.HITs.CauchyReals.Exponentiation.LogSequenceSquares

sq-bound-alg : ∀ t →
  (t -ᵣ 1) ·ᵣ (t -ᵣ 1) ·ᵣ (2 ·ᵣ t -ᵣ 1)
    ≡ t ·ᵣ ((2 ·ᵣ (t -ᵣ 1)) ·ᵣ (t -ᵣ 1))
       -ᵣ ((t -ᵣ 1) ·ᵣ (t -ᵣ 1))
sq-bound-alg t = ℝ!

tm1-times : ∀ t u → (t -ᵣ 1) ·ᵣ u ≡ (t ·ᵣ u) -ᵣ u
tm1-times t u = ℝ!

prod-one-minus : ∀ t u → (t -ᵣ 1) ·ᵣ (1 -ᵣ u) ≡ (t -ᵣ 1) -ᵣ ((t -ᵣ 1) ·ᵣ u)
prod-one-minus t u = ℝ!

lhs-sq/x-alg : ∀ t u → t ·ᵣ u ≡ 1 →
  (t -ᵣ 1) -ᵣ (1 -ᵣ u) ≡ ((t -ᵣ 1) ·ᵣ (t -ᵣ 1)) ·ᵣ u
lhs-sq/x-alg t u t·u≡1 = sym $
  ((t -ᵣ 1) ·ᵣ (t -ᵣ 1)) ·ᵣ u
    ≡⟨ sym (·ᵣAssoc (t -ᵣ 1) (t -ᵣ 1) u) ⟩
  (t -ᵣ 1) ·ᵣ ((t -ᵣ 1) ·ᵣ u)
    ≡⟨ cong ((t -ᵣ 1) ·ᵣ_) (tm1-times t u ∙ cong (_-ᵣ u) t·u≡1) ⟩
  (t -ᵣ 1) ·ᵣ (1 -ᵣ u)
    ≡⟨ prod-one-minus t u ⟩
  (t -ᵣ 1) -ᵣ ((t -ᵣ 1) ·ᵣ u)
    ≡⟨ cong (λ z → (t -ᵣ 1) -ᵣ z) (tm1-times t u ∙ cong (_-ᵣ u) t·u≡1) ⟩
  (t -ᵣ 1) -ᵣ (1 -ᵣ u) ∎

opaque
 unfolding invℝ
 x+1/x-bound : ∀ (x : ℝ₊) → rat [ 1 / 2 ] ≤ᵣ fst x →
    (fst x -ᵣ 1) -ᵣ (1 -ᵣ fst (invℝ₊ x))  ≤ᵣ (2 ·ᵣ (fst x -ᵣ 1)) ·ᵣ (fst x -ᵣ 1)
 x+1/x-bound x 1/2≤x =
   isTrans≡≤ᵣ _ _ _ (lhs-sq/x-alg xℝ invx (x·invℝ₊[x] x)) sq/x≤rhs

  where
  xℝ : ℝ
  xℝ = fst x

  invx : ℝ
  invx = fst (invℝ₊ x)

  sq : ℝ
  sq = (xℝ -ᵣ 1) ·ᵣ (xℝ -ᵣ 1)

  rhs : ℝ
  rhs = (2 ·ᵣ (xℝ -ᵣ 1)) ·ᵣ (xℝ -ᵣ 1)

  half-inv≤x : 1 ·ᵣ fst (invℝ₊ 2ℝ₊) ≤ᵣ xℝ
  half-inv≤x = isTrans≡≤ᵣ _ _ _
    (Rℝ.·IdL _
     ∙ cong (fst ∘ invℝ₊) (ℝ₊≡ {2ℝ₊} {ℚ₊→ℝ₊ 2₊} refl)
     ∙ invℝ₊-rat 2₊
     ∙ cong rat (invℚ₊-fromNat 1))
    1/2≤x

  0≤2x-1 : 0 ≤ᵣ (2 ·ᵣ xℝ) -ᵣ 1
  0≤2x-1 = fst (x≤y≃0≤y-x _ _)
    (fst (z/y≤x₊≃z≤y₊·x xℝ 1 2ℝ₊) half-inv≤x)

  h :  0  ≤ᵣ (fst x -ᵣ 1) ·ᵣ (fst x -ᵣ 1) ·ᵣ ((2 ·ᵣ x .fst) -ᵣ 1)
  h = isTrans≡≤ᵣ _ _ _ (rat·ᵣrat 0 0)
      (≤ᵣ₊Monotone·ᵣ 0 _ 0 _
        (0≤x·ᵣx _) (≤ᵣ-refl 0)
        (0≤x·ᵣx _) 0≤2x-1)

  sq≤x·rhs : sq ≤ᵣ xℝ ·ᵣ rhs
  sq≤x·rhs = invEq (x≤y≃0≤y-x sq (xℝ ·ᵣ rhs))
    (isTrans≤≡ᵣ _ _ _ h (sq-bound-alg xℝ))

  sq/x≤rhs : sq ·ᵣ invx ≤ᵣ rhs
  sq/x≤rhs = invEq (z/y≤x₊≃z≤y₊·x rhs sq x) sq≤x·rhs
