module Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Completion where

-- The completion and correspondence specifications. Inhabitants are
-- constructed in FundamentalTheorem.Completion, rather than assumed here.
-- The output is not a quotient of native vectors by exact matching.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_; equivFun; invEq)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Vec using (Vec; lookup; map)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties using (module PremetricTheory)
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Presented

-- Generic enough to reuse for the projective line. The base need only have
-- a closeness relation here: this record asks its inhabitant to establish a
-- separated premetric on the output and an isometric dense insertion.
record MatchingCompletion (A : Type₀) (close : A → ℚ₊ → A → Type₀)
  (n : ℕ) : Type₁ where
  field
    space : PremetricSpace ℓ-zero ℓ-zero

  Carrier : Type₀
  Carrier = fst space

  open PremetricStr (snd space) renaming (_≈[_]_ to _near[_]_) public

  field
    insert : Vec A n → Carrier
    insertionIsometry : ∀ xs ys ε →
      (insert xs near[ ε ] insert ys) ≃
      ∥ Σ[ σ ∈ (Fin n ≃ Fin n) ]
        ((i : Fin n) → close (lookup i xs) ε (lookup (equivFun σ i) ys)) ∥₁
    dense : ∀ x ε → ∥ Σ[ xs ∈ Vec A n ] (insert xs near[ ε ] x) ∥₁
    complete : PremetricTheory.isComplete space

    -- The modulus is already part of the witness. This field neither
    -- selects moduli from radiuswise truncations nor flattens native reals
    -- into rational sequences.
    sequentiallyComplete : (x : ℕ → Carrier) →
      ∥ PremetricTheory.isCauchySeq space x ∥₁ → PremetricTheory.limitSeq space x

RootMultisetCompletion : ℕ → Type₁
RootMultisetCompletion n = MatchingCompletion GaussianRational
  (λ a ε b → gaussianℂ a ∼ℂ[ ε ] gaussianℂ b) n

record CompletionCorrespondence (A B : Type₀)
  (baseClose : A → ℚ₊ → A → Type₀) (coefficientClose : B → ℚ₊ → B → Type₀)
  (n : ℕ) (finiteFactors : Vec A n → B) (C : MatchingCompletion A baseClose n) : Type₁ where
  private module M = MatchingCompletion C
  field
    factorEquivalence : M.Carrier ≃ B
    agreesOnFiniteFactors : (roots : Vec A n) →
      equivFun factorEquivalence (M.insert roots) ≡ finiteFactors roots

    -- The complete local modulus is inside a single truncation. This is
    -- stronger information than choosing δ separately for each ε.
    factorContinuity : (x : M.Carrier) → ∥ Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
      ((ε : ℚ₊) (y : M.Carrier) → x M.near[ μ ε ] y →
        coefficientClose (equivFun factorEquivalence x) ε (equivFun factorEquivalence y)) ∥₁
    rootContinuity : (p : B) → ∥ Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
      ((ε : ℚ₊) (q : B) → coefficientClose p (μ ε) q →
        invEq factorEquivalence p M.near[ ε ] invEq factorEquivalence q) ∥₁

RootMultisetCorrespondence : ∀ {n} → RootMultisetCompletion n → Type₁
RootMultisetCorrespondence {n} C = CompletionCorrespondence GaussianRational (MonicPolynomial n)
  (λ a ε b → gaussianℂ a ∼ℂ[ ε ] gaussianℂ b) CoefficientCloseness n
  (λ roots → linearFactors (map gaussianℂ roots)) C

-- Native target corresponding to Richman's completed-multiset FTA. The
-- completion structure is part of the OUTPUT, so this does not postulate
-- the missing object or smuggle its existence in as a theorem parameter.
CompletedMultisetFundamentalTheorem : Type₁
CompletedMultisetFundamentalTheorem = (n : ℕ) →
  Σ[ C ∈ RootMultisetCompletion n ] RootMultisetCorrespondence C
