module Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Projective where

-- Native target inspired by Richman's Theorem 6. Homogeneous degree is
-- fixed, but the coefficient of X^n may vanish. Roots at infinity are
-- retained. This is not a theorem about an arbitrary possibly-zero list.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_; equivFun; invEq)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin; zero; suc; toℕ)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup; map; zipWith)
import Cubical.Data.List as List
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
import Cubical.HITs.SetQuotients.Base as SQ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Relation.Premetric.Base using (IsPremetric)
open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base using (modulusℂ)
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Basic using (polynomialCoefficientℂ)
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Completion using (MatchingCompletion)

-- A phase-invariant coefficient l1 norm. This is a native alternative to
-- the equivalent finite-dimensional functional norm used in the paper.
homogeneousNorm : ∀ {k} → Vec ℂ k → ℝ
homogeneousNorm [] = 0ℝ
homogeneousNorm (a ∷ as) = modulusℂ a + homogeneousNorm as

UnitHomogeneous : ℕ → Type₀
UnitHomogeneous n = Σ[ coefficients ∈ Vec ℂ (suc n) ] homogeneousNorm coefficients ≡ 1ℝ

-- Vanishing 2x2 minors expresses projective equality on nonzero vectors.
-- Normalization supplies nonzeroness without a leading-coefficient test.
SameProjectiveRepresentative : ∀ {n} → UnitHomogeneous n → UnitHomogeneous n → Type₀
SameProjectiveRepresentative {n} a b = (i j : Fin (suc n)) →
  lookup i (fst a) ·ℂ lookup j (fst b) ≡ lookup j (fst a) ·ℂ lookup i (fst b)

ProjectivePolynomial : ℕ → Type₀
ProjectivePolynomial n = UnitHomogeneous n SQ./ (SameProjectiveRepresentative {n})

projectiveClass : ∀ {n} → UnitHomogeneous n → ProjectivePolynomial n
projectiveClass = SQ.[_]

ProjectiveClose : ∀ {n} → ProjectivePolynomial n → ℚ₊ → ProjectivePolynomial n → Type₀
ProjectiveClose {n} p ε q = ∥ Σ[ a ∈ UnitHomogeneous n ] Σ[ b ∈ UnitHomogeneous n ]
  ((projectiveClass a ≡ p) × (projectiveClass b ≡ q) ×
    (homogeneousNorm (zipWith _-ℂ_ (fst a) (fst b)) <ℝ rat (fst ε))) ∥₁

-- A point [u:v] is the root of v*X-u*Y. In particular [1:0] contributes
-- the factor -Y, the root at infinity, rather than being discarded.
homogeneousLinearFactors : ∀ {n} → Vec (UnitHomogeneous 1) n → List.List ℂ
homogeneousLinearFactors [] = 1ℂ List.∷ List.[]
homogeneousLinearFactors (r ∷ rs) = multiplyPolynomialsℂ
  ((-ℂ lookup zero (fst r)) List.∷ lookup (suc zero) (fst r) List.∷ List.[])
  (homogeneousLinearFactors rs)

RepresentsProjectiveProduct : ∀ {n} → Vec (UnitHomogeneous 1) n → ProjectivePolynomial n → Type₀
RepresentsProjectiveProduct {n} roots p = ∥ Σ[ a ∈ UnitHomogeneous n ]
  ((projectiveClass a ≡ p) × ((i j : Fin (suc n)) →
    polynomialCoefficientℂ (homogeneousLinearFactors roots) (toℕ i) ·ℂ lookup j (fst a) ≡
    polynomialCoefficientℂ (homogeneousLinearFactors roots) (toℕ j) ·ℂ lookup i (fst a))) ∥₁

module ProjectiveCorrespondence (n : ℕ)
  (rootCompletion : MatchingCompletion (ProjectivePolynomial 1) (ProjectiveClose {1}) n) where
  private module M = MatchingCompletion rootCompletion

  AgreesOnLinearFactors : (M.Carrier ≃ ProjectivePolynomial n) → Type₀
  AgreesOnLinearFactors factorEquivalence = (roots : Vec (UnitHomogeneous 1) n) →
      RepresentsProjectiveProduct roots
        (equivFun factorEquivalence (M.insert (map (projectiveClass {1}) roots)))

  UniformInBothDirections : (M.Carrier ≃ ProjectivePolynomial n) → Type₀
  UniformInBothDirections factorEquivalence =
    Σ[ factorModulus ∈ (ℚ₊ → ℚ₊) ] Σ[ rootModulus ∈ (ℚ₊ → ℚ₊) ]
      ((∀ x y ε → x M.near[ factorModulus ε ] y →
        ProjectiveClose {n} (equivFun factorEquivalence x) ε (equivFun factorEquivalence y)) ×
      (∀ p q ε → ProjectiveClose {n} p (rootModulus ε) q →
        invEq factorEquivalence p M.near[ ε ] invEq factorEquivalence q))

ProjectiveMultisetTheorem : ℕ → Type₁
ProjectiveMultisetTheorem n = IsPremetric (ProjectiveClose {n}) × IsPremetric (ProjectiveClose {1}) ×
  (Σ[ C ∈ MatchingCompletion (ProjectivePolynomial 1) (ProjectiveClose {1}) n ]
  Σ[ E ∈ (MatchingCompletion.Carrier C ≃ ProjectivePolynomial n) ]
    (ProjectiveCorrespondence.AgreesOnLinearFactors n C E ×
     ProjectiveCorrespondence.UniformInBothDirections n C E))

-- Both metric/completion construction and the uniformly bicontinuous
-- correspondence are requested as output. No inhabitant is asserted here.
ProjectiveFundamentalTheorem : Type₁
ProjectiveFundamentalTheorem = (n : ℕ) → ProjectiveMultisetTheorem n
