module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Approximate where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Geometric.Base
open import Cubical.Analysis.Real.Series.Geometric.Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Statement
open import Cubical.Analysis.Complex.FundamentalTheorem.Reduction
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Finite

private
  module R = RingTheory (CommRing→Ring ℝCommRing)

descent→approximateRoot : ∀ n q → 0ℝ ≤ℝ q → q <ℝ 1ℝ → PolynomialDescent n q →
  (p : MonicPolynomial (suc n)) (ε : ℚ₊) →
  ∥ Σ[ z ∈ ℂ ] evaluateMonic p z ∼ℂ[ ε ] 0ℂ ∥₁
descent→approximateRoot n q nonnegative below descend p ε =
  PT.rec squash₁ atThreshold (converges ε)
  where
  initial : ℝ
  initial = modulusℂ (evaluateMonic p 0ℂ)

  bound : ℝ
  bound = initial + 1ℝ

  initially-bounded : initial <ℝ bound
  initially-bounded = subst (_<ℝ bound) (addIdR initial)
    (<ℝ-addL 0ℝ 1ℝ initial (<ℚ→<ℝ 0 1 (ℚ.pos<pos tt)))

  converges : isLimitSequence (λ k → powℝ q k · bound) 0ℝ
  converges = subst (isLimitSequence (λ k → powℝ q k · bound)) (R.0LeftAnnihilates bound)
    (mulPresIsLimitSequence {x = geometricTerms q} {y = λ _ → bound} {l = 0ℝ} {m = bound}
      (realGeometricPowersTendToZero q
        (subst (_<ℝ 1ℝ) (sym (absOfNonnegative q nonnegative)) below))
      (constantIsLimitSequence bound))

  atThreshold : (Σ[ k ∈ ℕ ] (∀ j → k ℕ.≤ j → (powℝ q j · bound) ∼[ ε ] 0ℝ)) →
    ∥ Σ[ z ∈ ℂ ] evaluateMonic p z ∼ℂ[ ε ] 0ℂ ∥₁
  atThreshold (k , tail-close) = PT.map
    (λ (z , small) → z , modulusℂ-small→closeZero (evaluateMonic p z) ε
      (<ℝ-trans (modulusℂ (evaluateMonic p z)) (powℝ q k · bound) (rat (fst ε)) small small-bound))
    (finitePolynomialDescent n q descend p bound initially-bounded k)
    where
    small-bound : powℝ q k · bound <ℝ rat (fst ε)
    small-bound = ≤<ℝ-trans (powℝ q k · bound) (absℝ (powℝ q k · bound)) (rat (fst ε))
      (leAbs (powℝ q k · bound))
      (subst (_<ℝ rat (fst ε)) (cong absℝ (subZero (powℝ q k · bound)))
        (closeness→absDifference< (powℝ q k · bound) 0ℝ ε (tail-close k ℕ.≤-refl)))

-- A reusable reduction with an explicit mathematical hypothesis.
-- The Uniform module constructs the degree-dependent descent data.
uniformDescent→approximateRoots :
  ((n : ℕ) → Σ[ q ∈ ℝ ] (0ℝ ≤ℝ q) × (q <ℝ 1ℝ) × PolynomialDescent n q) →
  ApproximateRootExistence
uniformDescent→approximateRoots descent n =
  descent→approximateRoot n (fst (descent n)) (fst (snd (descent n)))
    (fst (snd (snd (descent n)))) (snd (snd (snd (descent n))))

uniformDescent→approximateFactorization :
  ((n : ℕ) → Σ[ q ∈ ℝ ] (0ℝ ≤ℝ q) × (q <ℝ 1ℝ) × PolynomialDescent n q) →
  ApproximateFundamentalTheorem
uniformDescent→approximateFactorization descent =
  approximateRoots→factorization (uniformDescent→approximateRoots descent)
