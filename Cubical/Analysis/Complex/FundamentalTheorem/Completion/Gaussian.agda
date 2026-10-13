module Cubical.Analysis.Complex.FundamentalTheorem.Completion.Gaussian where

-- Finite Gaussian-rational approximation is available without choosing a
-- presentation of any native real, or a family of approximations in ε.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup; map)
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base using (isSetℚ)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base using (rat-injective; rat-dense)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Presented

gaussian-injective : ∀ a b → gaussianℂ a ≡ gaussianℂ b → a ≡ b
gaussian-injective a b equal = cong₂ _,_
  (rat-injective (cong fst equal)) (rat-injective (cong snd equal))

private
  module G = SubspaceAlongInjection ℂPremetricSpace
    (isSet× isSetℚ isSetℚ) gaussianℂ gaussian-injective

gaussianSpace : PremetricSpace ℓ-zero ℓ-zero
gaussianSpace = G.injectionPremetricSpace

lookup-gaussian : ∀ {n} (qs : Vec GaussianRational n) (i : Fin n) →
  lookup i (map gaussianℂ qs) ≡ gaussianℂ (lookup i qs)
lookup-gaussian (q ∷ qs) zero = refl
lookup-gaussian (q ∷ qs) (suc i) = lookup-gaussian qs i

gaussian-dense : ∀ z ε → PT.∥ Σ[ q ∈ GaussianRational ] (gaussianℂ q ∼ℂ[ ε ] z) ∥₁
gaussian-dense z ε = PT.map2
  (λ { (a , real-close) (b , imag-close) → (a , b) , real-close , imag-close })
  (rat-dense (re z) ε) (rat-dense (im z) ε)

gaussian-vector-dense : ∀ {n} (zs : Vec ℂ n) ε →
  PT.∥ Σ[ qs ∈ Vec GaussianRational n ] CoefficientCloseness (map gaussianℂ qs) ε zs ∥₁
gaussian-vector-dense [] ε = PT.∣ [] , (λ ()) ∣₁
gaussian-vector-dense (z ∷ zs) ε = PT.map2
  (λ { (q , head) (qs , tail) → q ∷ qs , λ { zero → head ; (suc i) → tail i } })
  (gaussian-dense z ε) (gaussian-vector-dense zs ε)
