module Cubical.Analysis.Complex.FundamentalTheorem.Descent.OffDiagonal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Analysis.Real.Order.Structure
open import Cubical.Analysis.Real.Order.Strict.Continuity
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue using (addPres≤)
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.StrictOrder
open import Cubical.Analysis.Real.Functions.Powers.ExponentOrder
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.WeightedRoot
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Rescale
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.PowerDecay

private
  opaque
    reflectPositiveScale : ∀ x y s → 0ℝ <ℝ s → s · x <ℝ s · y → x <ℝ y
    reflectPositiveScale x y s positive below =
      continuousReflectsStrictOnOrderedInputs (s ·_) (mul-isContinuous₂ s) x y
        (O.·CancelL≤ x y s positive (<ℝ-weaken (s · x) (s · y) below)) below
      where
      module O = OrderedCommRingTheory ℝOrderedCommRing

    upperComparison : ∀ x y s t q ε E → 0ℝ ≤ℝ y → 0ℝ <ℝ s → s ≤ℝ q · t →
      s ≤ℝ 1ℝ → 0ℝ ≤ℝ ε → ε ≤ℝ E → x <ℝ y + ε → s · x <ℝ q · (t · y) + E
    upperComparison x y s t q ε E nonnegative positive factors small ε-nonnegative error below =
      <≤ℝ-trans (s · x) (s · y + s · ε) (q · (t · y) + E)
        (subst (s · x <ℝ_) (mulDistR s y ε) (mulPres<PosL x (y + ε) s positive below))
        (addPres≤ (s · y) (q · (t · y)) (s · ε) E
          (subst (s · y ≤ℝ_) (sym (mulAssoc q t y)) (mulPres≤R-0≤ s (q · t) y nonnegative factors))
          (≤ℝ-trans (s · ε) ε E
            (subst (s · ε ≤ℝ_) (mulIdL ε) (mulPres≤R-0≤ s 1ℝ ε ε-nonnegative small)) error))

    lowerComparison : ∀ x y s t q ε E → 0ℝ ≤ℝ y → 0ℝ <ℝ s → t ≤ℝ s · q →
      ε ≤ℝ s · E → s · x <ℝ t · y + ε → x <ℝ q · y + E
    lowerComparison x y s t q ε E nonnegative positive factors error below =
      reflectPositiveScale x (q · y + E) s positive
        (<≤ℝ-trans (s · x) (t · y + ε) (s · (q · y + E)) below
          (subst (t · y + ε ≤ℝ_) (sym (mulDistR s (q · y) E))
            (addPres≤ (t · y) (s · (q · y)) ε (s · E)
              (subst (t · y ≤ℝ_) (sym (mulAssoc s q y))
                (mulPres≤R-0≤ t (s · q) y nonnegative factors)) error)))

  oneIndexGap : ∀ q i j → 0ℝ <ℝ q → q ≤ℝ 1ℝ → i ℕ.< j →
    powℝ q (suc j) ≤ℝ q · powℝ q (suc i)
  oneIndexGap q i j positive small gap = powAntitoneExponent q (suc (suc i)) (suc j)
    (<ℝ-weaken 0ℝ q positive) small (ℕ.suc-≤-suc gap)

higherIndexBound : ∀ a b i k q r ε E → k ℕ.< i → 0ℝ ≤ℝ b →
  0ℝ <ℝ q → q ≤ℝ 1ℝ → 0ℝ ≤ℝ r → 0ℝ ≤ℝ ε → ε ≤ℝ E →
  weightedPower a i r <ℝ weightedPower b k r + ε →
  weightedPower a i (q · r) <ℝ q · weightedPower b k (q · r) + E
higherIndexBound a b i k q r ε E gap nonnegative positive small r-nonnegative ε-nonnegative error below =
  subst2 _<ℝ_ (sym (weightedPower-rescale a i q r))
    (cong (λ z → q · z + E) (sym (weightedPower-rescale b k q r)))
    (upperComparison (weightedPower a i r) (weightedPower b k r) (powℝ q (suc i)) (powℝ q (suc k)) q ε E
      (weightedPower-nonnegative b k r nonnegative r-nonnegative) (powPositive q (suc i) positive)
      (oneIndexGap q k i positive small gap) (powBelowOne q (suc i) (<ℝ-weaken 0ℝ q positive) small)
      ε-nonnegative error below)

lowerIndexBound : ∀ a b i k q r ε E → i ℕ.< k → 0ℝ ≤ℝ b →
  0ℝ <ℝ q → q ≤ℝ 1ℝ → 0ℝ ≤ℝ r → ε ≤ℝ powℝ q (suc i) · E →
  weightedPower a i (q · r) <ℝ weightedPower b k (q · r) + ε →
  weightedPower a i r <ℝ q · weightedPower b k r + E
lowerIndexBound a b i k q r ε E gap nonnegative positive small r-nonnegative error below =
  lowerComparison (weightedPower a i r) (weightedPower b k r) (powℝ q (suc i)) (powℝ q (suc k)) q ε E
    (weightedPower-nonnegative b k r nonnegative r-nonnegative) (powPositive q (suc i) positive)
    (subst (powℝ q (suc k) ≤ℝ_) (mulComm q (powℝ q (suc i))) (oneIndexGap q i k positive small gap))
    error (subst2 _<ℝ_ (weightedPower-rescale a i q r) (cong (_+ ε) (weightedPower-rescale b k q r)) below)
