module Cubical.Analysis.Real.Functions.Powers.Ring where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Functions.Powers

-- The native power function and generic ring power use the same recursion,
-- but are separate definitions. This bridge permits reuse of ring theorems.
opaque
  powℝ-as-ringPower : ∀ x n → powℝ x n ≡ Exponentiation._^_ ℝCommRing x n
  powℝ-as-ringPower x zero = refl
  powℝ-as-ringPower x (suc n) = cong (x ·_) (powℝ-as-ringPower x n)
