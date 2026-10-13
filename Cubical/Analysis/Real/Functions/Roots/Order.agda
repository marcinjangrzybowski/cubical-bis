module Cubical.Analysis.Real.Functions.Roots.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.StrictOrder
open import Cubical.Analysis.Real.Functions.Roots.Positive

positiveRootℝ-unique : ∀ n x positive y → 0ℝ ≤ℝ y → powℝ y (suc n) ≡ x →
  y ≡ positiveRootℝ n x positive
positiveRootℝ-unique n x positive y nonnegative equation =
  powInjectiveNonnegative n y (positiveRootℝ n x positive) nonnegative
    (<ℝ-weaken 0ℝ (positiveRootℝ n x positive) (positiveRootℝ-positive n x positive))
    (equation ∙ sym (positiveRootℝ-power n x positive))

positiveRootℝ-monotone : ∀ n x y xp yp → x ≤ℝ y →
  positiveRootℝ n x xp ≤ℝ positiveRootℝ n y yp
positiveRootℝ-monotone n x y xp yp ordered =
  powReflects≤Nonnegative n (positiveRootℝ n x xp) (positiveRootℝ n y yp)
    (<ℝ-weaken 0ℝ (positiveRootℝ n y yp) (positiveRootℝ-positive n y yp))
    (subst2 _≤ℝ_ (sym (positiveRootℝ-power n x xp)) (sym (positiveRootℝ-power n y yp)) ordered)

positiveRootℝ-strictlyIncreasing : ∀ n x y xp yp → x <ℝ y →
  positiveRootℝ n x xp <ℝ positiveRootℝ n y yp
positiveRootℝ-strictlyIncreasing n x y xp yp ordered =
  powReflects<Nonnegative n (positiveRootℝ n x xp) (positiveRootℝ n y yp)
    (<ℝ-weaken 0ℝ (positiveRootℝ n y yp) (positiveRootℝ-positive n y yp))
    (subst2 _<ℝ_ (sym (positiveRootℝ-power n x xp)) (sym (positiveRootℝ-power n y yp)) ordered)
