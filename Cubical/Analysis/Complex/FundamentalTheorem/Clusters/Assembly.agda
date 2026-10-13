module Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Assembly where

-- Exact coefficient identities for the empty and single-cluster cases.
-- A cluster may have repeated roots and arbitrarily large positive degree.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; +-zero)
import Cubical.Data.FinData as F
open import Cubical.Data.Vec using (Vec; []; _∷_)
open import Cubical.Data.Sigma
import Cubical.Data.Empty as Empty
open import Cubical.Algebra.CommRing using (module CommRingStr)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Differential.Monic
import Cubical.Analysis.Complex.Polynomial.Formal as Formal
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Basic using (PolynomialIdentityℂ)
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Clusters

private
  module P = Formal.Formal ℂCommRing
  module R = CommRingStr (snd P.polynomialRing)

emptyClusterFactorization : ∀ ε → ClusterFactorizationData [] ε
emptyClusterFactorization ε = zero , [] , refl , (λ k → refl) , (λ ()) , (λ ())

opaque
  singletonCluster-product : ∀ {n} (p : MonicPolynomial (suc n)) →
    PolynomialIdentityℂ (clusterProduct ((n , p) ∷ [])) (monicCoefficients p)
  singletonCluster-product {n} p = P.decode-identity (clusterProduct ((n , p) ∷ [])) (monicCoefficients p)
    (P.encode-multiply (monicCoefficients p) (monicCoefficients []) ∙ R.·IdR (P.encode (monicCoefficients p)))

singletonClusterFactorization : ∀ {n} (p : MonicPolynomial (suc n)) ε →
  SpectrumDiameterBelow p ε → ClusterFactorizationData p ε
singletonClusterFactorization {n} p ε small = 1 , ((n , p) ∷ []) ,
  +-zero (suc n) , singletonCluster-product p , (λ { F.zero → small }) ,
  (λ { F.zero F.zero unequal → Empty.rec (unequal refl) })
