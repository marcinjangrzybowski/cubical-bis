module Cubical.Analysis.Complex.FundamentalTheorem.Separable.Smallness where

-- Finite simultaneous error control. Coefficients may be zero: adding 1
-- before taking a reciprocal removes any need to decide their positivity.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Unit using (tt)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order using (positiveReciprocalPositive)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.SmallError using (smallPositiveRational3)

private
  one-positive : 0ℝ <ℝ 1ℝ
  one-positive = <ℚ→<ℝ 0 1 (ℚ.pos<pos tt)

  enlarge-positive : ∀ a → 0ℝ ≤ℝ a → 0ℝ <ℝ a + 1ℝ
  enlarge-positive a nonnegative = subst (_<ℝ a + 1ℝ) (addIdL 0ℝ)
    (≤<ℝ-add 0ℝ a 0ℝ 1ℝ nonnegative one-positive)

-- The output is one finite tuple inside truncation, not a function
-- choosing witnesses at all tolerances.
smallPositiveRationalForTwoProducts : ∀ x a b c d →
  0ℝ <ℝ x → 0ℝ ≤ℝ a → 0ℝ <ℝ b → 0ℝ ≤ℝ c → 0ℝ <ℝ d →
  PT.∥ Σ[ ε ∈ ℚ₊ ] (rat (fst ε) ≤ℝ x) ×
    (a · rat (fst ε) ≤ℝ b) × (c · rat (fst ε) ≤ℝ d) ∥₁
smallPositiveRationalForTwoProducts x a b c d xp an bp cn dp =
  PT.map (λ (ε , first , second , third) → ε , first ,
    control a b an ε second , control c d cn ε third)
    (smallPositiveRational3 x (reciprocal a an · b) (reciprocal c cn · d) xp
      (mulPositive (reciprocal a an) b (positiveReciprocalPositive (a + 1ℝ) (enlarge-positive a an)) bp)
      (mulPositive (reciprocal c cn) d (positiveReciprocalPositive (c + 1ℝ) (enlarge-positive c cn)) dp))
  where
  reciprocal : ∀ a → 0ℝ ≤ℝ a → ℝ
  reciprocal a nonnegative = positiveReciprocal (a + 1ℝ) (enlarge-positive a nonnegative)

  control : ∀ a b (nonnegative : 0ℝ ≤ℝ a) (ε : ℚ₊) →
    rat (fst ε) ≤ℝ reciprocal a nonnegative · b → a · rat (fst ε) ≤ℝ b
  control a b nonnegative ε bounded =
    ≤ℝ-trans (a · rat (fst ε)) ((a + 1ℝ) · rat (fst ε)) b
      (mulPres≤R-0≤ a (a + 1ℝ) (rat (fst ε)) (<ℝ-weaken 0ℝ (rat (fst ε)) (<ℚ→<ℝ 0 (fst ε) (snd ε)))
        (subst (_≤ℝ a + 1ℝ) (addIdR a)
          (addPres≤L 0ℝ 1ℝ a (<ℝ-weaken 0ℝ 1ℝ one-positive))))
      (subst ((a + 1ℝ) · rat (fst ε) ≤ℝ_) cancel
        (mulPres≤L (rat (fst ε)) (reciprocal a nonnegative · b) (a + 1ℝ)
          (0≤→isNonnegative (a + 1ℝ) (<ℝ-weaken 0ℝ (a + 1ℝ) (enlarge-positive a nonnegative))) bounded))
    where
    cancel : (a + 1ℝ) · (reciprocal a nonnegative · b) ≡ b
    cancel = mulAssoc (a + 1ℝ) (reciprocal a nonnegative) b
      ∙ cong (_· b) (positiveReciprocalLaw (a + 1ℝ) (enlarge-positive a nonnegative)) ∙ mulIdL b
