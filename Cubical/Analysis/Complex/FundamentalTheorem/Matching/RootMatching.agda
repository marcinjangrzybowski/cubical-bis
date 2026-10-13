module Cubical.Analysis.Complex.FundamentalTheorem.Matching.RootMatching where

-- Match one pair, remove it by synthetic division, and induct on degree.
-- All bounds are explicit functions of degree, a common rational bound,
-- and the requested radius. Finite truncations stay inside MatchingClose.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_; equivFun; idEquiv; compEquiv)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup; drop)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; min₊; min₊≤L; min₊≤R)
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
import Cubical.Analysis.Complex.Polynomial.Monic.DeflationAlgebra as DeflationDefinition
import Cubical.Analysis.Complex.Polynomial.Monic.PermutationAlgebra as PermutationDefinition
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Finite
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Evaluation
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.FactorContinuity
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.NearRoot
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.RootBounds
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Perturbation

private
  module C = PremetricStr (ℂPremetricSpace .snd)
  module D = DeflationDefinition.Deflation ℂCommRing
  module P = PermutationDefinition.Permutation ℂCommRing

-- The internal induction retains the original bound on every remaining
-- root. Bounds on the deflated coefficients then come from finite factor
-- multiplication, so they need not remain below the original coefficient
-- bound.
boundedMatchingModulus : ℕ → ℚ₊ → ℚ₊ → ℚ₊
boundedMatchingModulus zero B ε = ε
boundedMatchingModulus (suc n) B ε = min₊ α (scaleTolerance E (smallProductThreshold (suc n) (min₊ ε α)))
  where
  A = factorCoefficientBound (suc n) B
  α = scaleTolerance (monicQuotientLipschitz n A B) (boundedMatchingModulus n B ε)
  E = monicEvaluationLipschitz (suc n) A B

opaque
  boundedRootMatching : ∀ n B ε (roots roots′ : Vec ℂ n) →
    RootsBounded roots B → RootsBounded roots′ B →
    CoefficientCloseness (linearFactors roots) (boundedMatchingModulus n B ε) (linearFactors roots′) →
    MatchingClose roots ε roots′
  boundedRootMatching zero B ε [] [] rb sb close = PT.∣ idEquiv (Fin zero) , (λ ()) ∣₁
  boundedRootMatching (suc n) B ε (r ∷ roots) roots′ rb sb close =
    PT.rec PT.isPropPropTrunc select
      (smallProduct-nearRoot roots′ r η
        (monicEvaluation-nearZero p q r A B τ (linearFactors-bound roots′ B sb) (rb zero)
          (linearFactors-root (r ∷ roots) zero)
          (coefficientCloseness-monotone p q δ (scaleTolerance E τ) (min₊≤R α (scaleTolerance E τ)) close)))
    where
    p q : MonicPolynomial (suc n)
    p = linearFactors (r ∷ roots)
    q = linearFactors roots′
    A tailTolerance α η E τ δ : ℚ₊
    A = factorCoefficientBound (suc n) B
    tailTolerance = boundedMatchingModulus n B ε
    α = scaleTolerance (monicQuotientLipschitz n A B) tailTolerance
    η = min₊ ε α
    E = monicEvaluationLipschitz (suc n) A B
    τ = smallProductThreshold (suc n) η
    δ = min₊ α (scaleTolerance E τ)

    select : (Σ[ i ∈ Fin (suc n) ] (r ∼ℂ[ η ] lookup i roots′)) → MatchingClose (r ∷ roots) ε roots′
    select (i , near) = PT.map assemble
      (boundedRootMatching n B ε roots (drop i roots′) (λ j → rb (suc j)) (dropRootsBounded roots′ i B sb)
        deflated-close)
      where
      s : ℂ
      s = lookup i roots′
      deflated-close : CoefficientCloseness (linearFactors roots) tailTolerance (linearFactors (drop i roots′))
      deflated-close = subst2 (λ u v → CoefficientCloseness u tailTolerance v)
        (D.quotient-multiplyLinear r (linearFactors roots))
        (cong (λ f → quotientMonic f s) (P.linearFactors-extract roots′ i)
          ∙ D.quotient-multiplyLinear s (linearFactors (drop i roots′)))
        (monicQuotient-closeness p q r s A B tailTolerance (linearFactors-bound (r ∷ roots) B rb)
          (rb zero) (sb i)
          (coefficientCloseness-monotone p q δ α (min₊≤L α (scaleTolerance E τ)) close)
          (C.isMonotone≈≤ r s η α (min₊≤R ε α) near))

      assemble : (Σ[ σ ∈ (Fin n ≃ Fin n) ]
        (∀ j → lookup j roots ∼ℂ[ ε ] lookup (equivFun σ j) (drop i roots′))) →
        Σ[ σ ∈ (Fin (suc n) ≃ Fin (suc n)) ]
          (∀ j → lookup j (r ∷ roots) ∼ℂ[ ε ] lookup (equivFun σ j) roots′)
      assemble (σ , matched) = compEquiv (liftPermutation σ) (extractPermutation i) , complete
        where
        complete : ∀ j → lookup j (r ∷ roots) ∼ℂ[ ε ]
          lookup (equivFun (extractPermutation i) (equivFun (liftPermutation σ) j)) roots′
        complete zero = subst (r ∼ℂ[ ε ]_) (sym (cong (λ j → lookup j roots′) (extract-zero i)))
          (C.isMonotone≈≤ r s η ε (min₊≤L ε α) near)
        complete (suc j) = subst (lookup j roots ∼ℂ[ ε ]_)
          (extract-lookup roots′ i (suc (equivFun σ j))) (matched j)

rootMatchingModulus : ℕ → ℚ₊ → ℚ₊ → ℚ₊
rootMatchingModulus n A ε = boundedMatchingModulus n (coefficientRootBound n A) ε

rootMatchingEstimate : RootMatchingEstimate rootMatchingModulus
rootMatchingEstimate n A ε roots roots′ pb qb = boundedRootMatching n (coefficientRootBound n A) ε roots roots′
  (factorRootsBounded roots A pb) (factorRootsBounded roots′ A qb)

quantitativeRootMatching : QuantitativeRootMatching
quantitativeRootMatching = rootMatchingModulus , rootMatchingEstimate
