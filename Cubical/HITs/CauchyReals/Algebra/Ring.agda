module Cubical.HITs.CauchyReals.Algebra.Ring where

open import Cubical.Foundations.Prelude

import Cubical.Data.Nat as ℕ
open import Cubical.Data.Unit

import Cubical.Algebra.CommRing as CR
import Cubical.Algebra.Ring as RP
open import Cubical.Algebra.Group using (Group₀)

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Algebra.Multiplication


module Rℝ where
  ℝRing = CR.CommRing→Ring ℝcommRing
  open CR.CommRingStr (snd ℝcommRing) public
  open RP.RingTheory ℝRing public
  open CR.CommRingTheory ℝcommRing public


+Groupℝ : Group₀
+Groupℝ = RP.Ring→Group Rℝ.ℝRing


private
  realFromNat : ℕ.ℕ → ℝ
  realFromNat n = ℕ.HasFromNat.fromNat fromNatℝ n {{tt}}


fromℕ≡fromNatℝ : ∀ n → Rℝ.fromℕ n ≡ realFromNat n
fromℕ≡fromNatℝ ℕ.zero = refl
fromℕ≡fromNatℝ (ℕ.suc ℕ.zero) = refl
fromℕ≡fromNatℝ (ℕ.suc (ℕ.suc n)) =
  cong (realFromNat (ℕ.suc ℕ.zero) +ᵣ_) (fromℕ≡fromNatℝ (ℕ.suc n))
  ∙ fromNat+ᵣ (ℕ.suc ℕ.zero) (ℕ.suc n)


x+n·x≡sn·x : ∀ n x → x +ᵣ fromNat n ·ᵣ x ≡ fromNat (ℕ.suc n) ·ᵣ x
x+n·x≡sn·x n x = cong₂ _+ᵣ_
  (sym (·IdLᵣ _)) refl ∙ sym (·DistR+ _ _ _)
  ∙ cong (_·ᵣ x) (fromNat+ᵣ 1 n)


-ᵣ≡[-1·ᵣ] : ∀ x → -ᵣ x ≡ (-1) ·ᵣ x
-ᵣ≡[-1·ᵣ] x =
  Rℝ.-IsMult-1 x ∙ cong (_·ᵣ x) (-ᵣ-rat 1)
