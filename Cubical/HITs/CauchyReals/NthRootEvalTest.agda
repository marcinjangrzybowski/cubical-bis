module Cubical.HITs.CauchyReals.NthRootEvalTest where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
import Cubical.Data.Nat.Order as ℕ
import Cubical.Data.Nat.Order.Inductive as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast as ℤ using (pos; ℤ)
import Cubical.Data.Int.Fast.Order as ℤ

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding ([_])

open import Cubical.Data.NatPlusOne


open import Cubical.HITs.CauchyReals.Base

open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Lipschitz
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.Sequence
open import Cubical.HITs.CauchyReals.Bisection
open import Cubical.HITs.CauchyReals.RationalsImports
open import Cubical.Data.Rationals.Bisection as ℚB
open import Cubical.HITs.CauchyReals.NthRoot
open import Cubical.HITs.CauchyReals.Aproximations

open ℚ using (invℚ)



module _ where
 open NthRoot
 opaque
  unfolding nth-root ℝ₊⊆rootSeq
  t0 : fst (root 2 (ℚ₊→ℝ₊ 4)) d🪄 2
  t0 = digitsℝ (fst (root 2 (ℚ₊→ℝ₊ 4)))  2


  t0' : fst (root 2 (ℚ₊→ℝ₊ 4)) d🪄 2
  t0' = {!t0!}


