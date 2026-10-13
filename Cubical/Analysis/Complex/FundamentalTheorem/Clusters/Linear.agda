module Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Linear where

-- The cluster specification is inhabited for an exact factorization into
-- pairwise apart roots. This is the separated linear case, not the general
-- small-separated-factor theorem for arbitrary polynomials.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.FinData as F
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing using (module CommRingStr)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Distance
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Differential.Monic
import Cubical.Analysis.Complex.Polynomial.Formal as Formal
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Basic
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Clusters
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Separable.Factorization
open import Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Certificates

linearClusters : ∀ {n} → Vec ℂ n → Vec PositiveMonicPolynomial n
linearClusters [] = []
linearClusters (r ∷ roots) = (zero , linearFactors (r ∷ [])) ∷ linearClusters roots

private
  module P = Formal.Formal ℂCommRing
  module R = CommRingStr (snd P.polynomialRing)

  lookup-linearClusters : ∀ {n} (roots : Vec ℂ n) i →
    lookup i (linearClusters roots) ≡ (zero , linearFactors (lookup i roots ∷ []))
  lookup-linearClusters (r ∷ roots) F.zero = refl
  lookup-linearClusters (r ∷ roots) (F.suc i) = lookup-linearClusters roots i

  linearClusters-degree : ∀ {n} (roots : Vec ℂ n) → clusterDegree (linearClusters roots) ≡ n
  linearClusters-degree [] = refl
  linearClusters-degree (r ∷ roots) = cong suc (linearClusters-degree roots)

  opaque
    linearClusters-encode : ∀ {n} (roots : Vec ℂ n) →
      P.encode (clusterProduct (linearClusters roots)) ≡ P.monicValue (linearFactors roots)
    linearClusters-encode [] = refl
    linearClusters-encode (r ∷ roots) =
      P.encode-multiply (monicCoefficients (linearFactors (r ∷ []))) (clusterProduct (linearClusters roots))
      ∙ cong₂ R._·_ (P.encode-linear r) (linearClusters-encode roots)
      ∙ sym (P.monicValue-multiplyLinear r (linearFactors roots))

    linearClusters-product : ∀ {n} (roots : Vec ℂ n) →
      PolynomialIdentityℂ (clusterProduct (linearClusters roots)) (monicCoefficients (linearFactors roots))
    linearClusters-product roots = P.decode-identity (clusterProduct (linearClusters roots))
      (monicCoefficients (linearFactors roots))
      (linearClusters-encode roots ∙ sym (P.encode-monic (linearFactors roots)))

linear-spectrum-small : ∀ r ε → SpectrumDiameterBelow (linearFactors (r ∷ [])) ε
linear-spectrum-small r ε = finite-diameter→spectrum (r ∷ []) ε
  (λ { F.zero F.zero → subst (_<ℝ ⟦ ε ⟧₊) (sym (distanceℂ-refl r)) (radius-positive ε) })

apart-linear-spectra : ∀ r s → 0ℝ <ℝ distanceℂ r s →
  SpectraSeparated (linearFactors (r ∷ [])) (linearFactors (s ∷ []))
apart-linear-spectra r s apart = finite-apart→spectra (r ∷ []) (s ∷ [])
  (λ { F.zero F.zero → apart })

linearClusterFactorization : ∀ {n} (roots : Vec ℂ n) ε → PairwiseApartRoots roots →
  ClusterFactorizationData (linearFactors roots) ε
linearClusterFactorization {n} roots ε apart = n , linearClusters roots ,
  linearClusters-degree roots , linearClusters-product roots ,
  (λ i → subst (λ factor → SpectrumDiameterBelow (snd factor) ε)
    (sym (lookup-linearClusters roots i)) (linear-spectrum-small (lookup i roots) ε)) ,
  (λ i j unequal → subst2 (λ first second → SpectraSeparated (snd first) (snd second))
    (sym (lookup-linearClusters roots i)) (sym (lookup-linearClusters roots j))
    (apart-linear-spectra (lookup i roots) (lookup j roots) (apart i j unequal)))

stronglySeparableClusterFactorization : ∀ n (p : MonicPolynomial n) ε → StronglySeparable p →
  PT.∥ ClusterFactorizationData p ε ∥₁
stronglySeparableClusterFactorization n p ε separable = PT.map
  (λ { (roots , equal , apart) → subst (λ q → ClusterFactorizationData q ε) equal
    (linearClusterFactorization roots ε apart) })
  (stronglySeparableFundamentalTheorem n p separable)
