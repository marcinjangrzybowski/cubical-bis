{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.FiniteRisk where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ; ℚ!)
import Cubical.Data.FinData.Base as F
import Cubical.Experiments.Relation.Aggregation as Aggregation

module QSum = Aggregation.Sum ℚ 0 ℚ._+_

-- The relational fold and the financial fold use the same finite order.
-- This bridge preserves the exact value, including the empty sum.
rat-finiteSum : ∀ {n} (values : Fin n → ℚ) →
  rat (QSum.finiteSum values) ≡ sum (λ i → rat (values i))
rat-finiteSum {zero} values = refl
rat-finiteSum {suc n} values = sym (+ᵣ-rat _ _)
  ∙ cong (rat (values F.zero) +ᵣ_) (rat-finiteSum (λ i → values (F.suc i)))

finiteSum-zero : ∀ n → QSum.finiteSum {n} (λ _ → 0) ≡ 0
finiteSum-zero zero = refl
finiteSum-zero (suc n) = cong (0 ℚ.+_) (finiteSum-zero n) ∙ ℚ.+IdL 0

finiteSum-nonnegative : ∀ {n} (values : Fin n → ℚ) →
  (∀ i → 0 ℚ.≤ values i) → 0 ℚ.≤ QSum.finiteSum values
finiteSum-nonnegative values nonnegative = ≤ᵣ→≤ℚ 0 _
  (isTrans≤≡ᵣ _ _ _
    (sum-nonnegative (λ i → rat (values i)) (λ i → ≤ℚ→≤ᵣ 0 _ (nonnegative i)))
    (sym (rat-finiteSum values)))

private
  member≤sum : ∀ {n} (values : Vector n) →
    (∀ i → 0 ≤ᵣ values i) → ∀ i → values i ≤ᵣ sum values
  member≤sum {suc n} values nonnegative F.zero = isTrans≡≤ᵣ _ _ _
    (sym (+IdR (values F.zero)))
    (≤ᵣ-o+ _ _ (values F.zero)
      (sum-nonnegative (λ i → values (F.suc i)) (λ i → nonnegative (F.suc i))))
  member≤sum {suc n} values nonnegative (F.suc i) = isTrans≤ᵣ _ _ _
    (member≤sum (λ j → values (F.suc j)) (λ j → nonnegative (F.suc j)) i)
    (isTrans≡≤ᵣ _ _ _ (sym (+IdL (sum (λ j → values (F.suc j)))))
      (≤ᵣ-+o 0 (values F.zero) (sum (λ j → values (F.suc j))) (nonnegative F.zero)))

finiteSum-member-bound : ∀ {n} (values : Fin n → ℚ) →
  (∀ i → 0 ℚ.≤ values i) → ∀ i →
  rat (values i) ≤ᵣ rat (QSum.finiteSum values)
finiteSum-member-bound values nonnegative i = isTrans≤≡ᵣ _ _ _
  (member≤sum (λ j → rat (values j)) (λ j → ≤ℚ→≤ᵣ 0 _ (nonnegative j)) i)
  (sym (rat-finiteSum values))

-- A deliberately conservative executable reserve: sum the positive changes
-- over every indexed scenario. This bounds each adverse change, but is not
-- asserted to be the least uniform reserve or a probability-weighted loss.
differenceReserve : ∀ {n} → (Fin n → ℚ) → (Fin n → ℚ) → ℚ
differenceReserve old new = QSum.finiteSum (λ i → ℚ.max (new i ℚ.- old i) 0)

differenceReserve-nonnegative : ∀ {n} (old new : Fin n → ℚ) →
  0 ℚ.≤ differenceReserve old new
differenceReserve-nonnegative old new = finiteSum-nonnegative _
  (λ i → ℚ.≤max' (new i ℚ.- old i) 0)

differenceReserve-covers : ∀ {n} (old new : Fin n → ℚ) i →
  rat (new i) ≤ᵣ rat (old i) +ᵣ rat (differenceReserve old new)
differenceReserve-covers old new i = isTrans≤ᵣ _ _ _
  (stopLoss-reconstruct (rat (new i)) (rat (old i)))
  (≤ᵣ-o+ _ _ (rat (old i))
    (isTrans≡≤ᵣ _ _ _ (stopLoss-rat (new i) (old i))
      (finiteSum-member-bound (λ j → ℚ.max (new j ℚ.- old j) 0)
        (λ j → ℚ.≤max' (new j ℚ.- old j) 0) i)))

differenceReserve-self : ∀ {n} (old : Fin n → ℚ) → differenceReserve old old ≡ 0
differenceReserve-self {n} old = cong QSum.finiteSum
  (funExt (λ i → cong (λ x → ℚ.max x 0) (self-difference (old i)) ∙ ℚ.maxIdem 0))
  ∙ finiteSum-zero n
  where
  self-difference : ∀ x → x ℚ.- x ≡ 0
  self-difference x = ℚ!
