module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Radii where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Functions.Powers

-- Tail recursion follows the finite near-maximum chain literally.
shrinkRadius : ℝ → ℕ → ℝ → ℝ
shrinkRadius q zero r = r
shrinkRadius q (suc steps) r = shrinkRadius q steps (q · r)

shrinkRadius-positive : ∀ q steps r → 0ℝ <ℝ q → 0ℝ <ℝ r → 0ℝ <ℝ shrinkRadius q steps r
shrinkRadius-positive q zero r q-positive r-positive = r-positive
shrinkRadius-positive q (suc steps) r q-positive r-positive =
  shrinkRadius-positive q steps (q · r) q-positive (mulPositive q r q-positive r-positive)

shrinkRadius≤initial : ∀ q steps r → 0ℝ <ℝ q → q ≤ℝ 1ℝ → 0ℝ <ℝ r → shrinkRadius q steps r ≤ℝ r
shrinkRadius≤initial q zero r q-positive q-small r-positive = ≤ℝ-refl r
shrinkRadius≤initial q (suc steps) r q-positive q-small r-positive =
  ≤ℝ-trans (shrinkRadius q steps (q · r)) (q · r) r
    (shrinkRadius≤initial q steps (q · r) q-positive q-small (mulPositive q r q-positive r-positive))
    (subst (q · r ≤ℝ_) (mulIdL r)
      (mulPres≤R-0≤ q 1ℝ r (<ℝ-weaken 0ℝ r r-positive) q-small))

shrinkRadius-equation : ∀ q steps r → shrinkRadius q steps r ≡ powℝ q steps · r
shrinkRadius-equation q zero r = sym (mulIdL r)
shrinkRadius-equation q (suc steps) r = shrinkRadius-equation q steps (q · r)
  ∙ mulAssoc (powℝ q steps) q r ∙ cong (_· r) (mulComm (powℝ q steps) q)

shrinkRadius-step : ∀ q steps r → shrinkRadius q (suc steps) r ≡ q · shrinkRadius q steps r
shrinkRadius-step q steps r = shrinkRadius-equation q (suc steps) r
  ∙ sym (mulAssoc q (powℝ q steps) r) ∙ cong (q ·_) (sym (shrinkRadius-equation q steps r))
