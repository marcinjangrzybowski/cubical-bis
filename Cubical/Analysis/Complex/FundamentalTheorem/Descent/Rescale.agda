module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Rescale where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Algebra.CommRing
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Functions.Powers.StrictOrder
open import Cubical.Analysis.Real.Functions.Powers.ExponentOrder
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.WeightedRoot

private
  module P = Exponentiation ℝCommRing

  nativePower : ∀ x n → x P.^ n ≡ powℝ x n
  nativePower x zero = refl
  nativePower x (suc n) = cong (x ·_) (nativePower x n)

  powerProduct : ∀ x y n → powℝ (x · y) n ≡ powℝ x n · powℝ y n
  powerProduct x y n = sym (nativePower (x · y) n) ∙ P.^-ldist-· x y n
    ∙ cong₂ _·_ (nativePower x n) (nativePower y n)

  scaleComparison : ∀ x y s t ε δ → 0ℝ ≤ℝ y → 0ℝ <ℝ s → s ≤ℝ t →
    s · ε ≤ℝ δ → x <ℝ y + ε → s · x <ℝ t · y + δ
  scaleComparison x y s t ε δ nonnegative positive ordered error close =
    <≤ℝ-trans (s · x) (s · y + s · ε) (t · y + δ)
      (subst (s · x <ℝ_) (mulDistR s y ε) (mulPres<PosL x (y + ε) s positive close))
      (addPres≤ (s · y) (t · y) (s · ε) δ (mulPres≤R-0≤ s t y nonnegative ordered) error)

weightedPower-rescale : ∀ a n q r →
  weightedPower a n (q · r) ≡ powℝ q (suc n) · weightedPower a n r
weightedPower-rescale a n q r = cong (a ·_) (powerProduct q r (suc n))
  ∙ mulAssoc a (powℝ q (suc n)) (powℝ r (suc n))
  ∙ cong (_· powℝ r (suc n)) (mulComm a (powℝ q (suc n)))
  ∙ sym (mulAssoc (powℝ q (suc n)) a (powℝ r (suc n)))

-- A higher-index competitor remains below a lower-index approximate
-- maximizer after rescaling. The old comparison error contracts by q.
rescaledNearMaximum : ∀ a b i j q r ε δ →
  0ℝ ≤ℝ b → j ℕ.≤ i → 0ℝ <ℝ q → q ≤ℝ 1ℝ → 0ℝ ≤ℝ r → 0ℝ ≤ℝ ε →
  q · ε ≤ℝ δ → weightedPower a i r <ℝ weightedPower b j r + ε →
  weightedPower a i (q · r) <ℝ weightedPower b j (q · r) + δ
rescaledNearMaximum a b i j q r ε δ b-nonnegative indices q-positive q-small r-nonnegative ε-nonnegative error close =
  subst2 _<ℝ_ (sym (weightedPower-rescale a i q r))
    (cong (_+ δ) (sym (weightedPower-rescale b j q r)))
    (scaleComparison (weightedPower a i r) (weightedPower b j r)
      (powℝ q (suc i)) (powℝ q (suc j)) ε δ
      (isNonnegative→0≤ (weightedPower b j r)
        (mulPresIsNonnegative b (powℝ r (suc j)) (0≤→isNonnegative b b-nonnegative)
          (powPresIsNonnegative r (suc j) (0≤→isNonnegative r r-nonnegative))))
      (powPositive q (suc i) q-positive)
      (powAntitoneExponent q (suc j) (suc i) (<ℝ-weaken 0ℝ q q-positive) q-small (ℕ.suc-≤-suc indices))
      (≤ℝ-trans (powℝ q (suc i) · ε) (q · ε) δ
        (mulPres≤R-0≤ (powℝ q (suc i)) q ε ε-nonnegative
          (powPositiveExponent≤Base q i (<ℝ-weaken 0ℝ q q-positive) q-small)) error)
      close)
