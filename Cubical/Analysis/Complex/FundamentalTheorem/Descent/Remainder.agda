module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Remainder where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Data.FinData as Fin using (Fin)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.WeightedRoot
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.PowerDecay
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Shrink
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.DegreeShrink
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.ErrorAllowance
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.SelectedTerm
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Dominance
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.FiniteSum

dominantRemainderBound : ∀ {n} (values : Fin (suc n) → ℝ) k ε → 0ℝ ≤ℝ values k →
  (∀ i → ¬ (i ≡ k) → values i <ℝ degreeShrink n · values k + degreeErrorAllowance n ε) →
  sumOtherRealTerms values k ≤ℝ descentShrink · values k + realNatural (suc n) · degreeErrorAllowance n ε
dominantRemainderBound {n} values k ε nonnegative bounded =
  ≤ℝ-trans (sumOtherRealTerms values k) (N · (q · s + E)) (descentShrink · s + N · E)
    (sumOtherRealTerms-countBound values k (q · s + E) bound-nonnegative
      (λ i different → <ℝ-weaken (values i) (q · s + E) (bounded i different)))
    (subst (_≤ℝ descentShrink · s + N · E)
      (sym (mulDistR N (q · s) E ∙ cong (_+ N · E) (mulAssoc N q s)))
      (addPres≤ (N · q · s) (descentShrink · s) (N · E) (N · E)
        (mulPres≤R-0≤ (N · q) descentShrink s nonnegative (degreeShrink-countBound n)) (≤ℝ-refl (N · E))))
  where
  N = realNatural (suc n)
  q = degreeShrink n
  s = values k
  E = degreeErrorAllowance n ε
  module Error = PowerErrorAllowance n q (degreeShrink-positive n) (rat (fst ε))

  bound-nonnegative : 0ℝ ≤ℝ q · s + E
  bound-nonnegative = isNonnegative→0≤ (q · s + E)
    (addPresIsNonnegative (q · s) E
      (mulPresIsNonnegative q s
        (0≤→isNonnegative q (<ℝ-weaken 0ℝ q (degreeShrink-positive n))) (0≤→isNonnegative s nonnegative))
      (0≤→isNonnegative E (Error.allowance-nonnegative
        (<ℝ-weaken 0ℝ (rat (fst ε)) (<ℚ→<ℝ 0 (fst ε) (snd ε))))))

PowerRemainderScale : ∀ {n} → Vec ℝ (suc n) → ℝ → ℚ₊ → Type₀
PowerRemainderScale {n} coefficients target ε = Σ[ r ∈ ℝ ] (0ℝ <ℝ r) ×
  (Σ[ k ∈ Fin (suc n) ]
    (selectedTermFactor n (degreeShrink n) · target <ℝ weight r k + rat (fst ε)) ×
    (weight r k <ℝ target + rat (fst ε)) ×
    (sumOtherRealTerms (weight r) k ≤ℝ descentShrink · weight r k +
      realNatural (suc n) · degreeErrorAllowance n ε))
  where
  weight : ℝ → Fin (suc n) → ℝ
  weight r i = weightedPower (lookup i coefficients) (Fin.toℕ i) r

-- A quantitative scale and coefficient exist for every positive target
-- and requested error. Only finite propositional-truncation elimination is used.
finitePowerRemainderScale : ∀ {n} (coefficients : Vec ℝ (suc n)) →
  (∀ i → 0ℝ ≤ℝ lookup i coefficients) → 0ℝ <ℝ lookup (Fin.fromℕ n) coefficients →
  (target : ℝ) → 0ℝ <ℝ target → (ε : ℚ₊) → ∥ PowerRemainderScale coefficients target ε ∥₁
finitePowerRemainderScale coefficients nonnegative leading-positive target target-positive ε = PT.map fromDominant
  (finiteDominantPowerScale coefficients nonnegative leading-positive target target-positive ε)
  where
  fromDominant : DominantPowerScale coefficients target ε → PowerRemainderScale coefficients target ε
  fromDominant (r , positive , k , selected-lower , selected-upper , others) =
    r , positive , k , selected-lower , selected-upper ,
      dominantRemainderBound (λ i → weightedPower (lookup i coefficients) (Fin.toℕ i) r) k ε
        (weightedPower-nonnegative (lookup k coefficients) (Fin.toℕ k) r (nonnegative k) (<ℝ-weaken 0ℝ r positive)) others
