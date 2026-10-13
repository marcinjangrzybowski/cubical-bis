module Cubical.Analysis.Complex.Integration.LineIntegral.Reparameterization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
open import Cubical.Analysis.Complex.Integration.Base
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Reparameterization
open import Cubical.Analysis.Complex.Integration.Substitution
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.FundamentalTheorem
open import Cubical.Analysis.Complex.Integration.LineIntegral.Bounded

module _ {a b c d : ℝ} (path : UniformComplexPath c d) (change : UniformParameterChange a b)
  (imageLower : ∀ t → a ≤ℝ t → t ≤ℝ b → c ≤ℝ UniformParameterChange.curve change t)
  (imageUpper : ∀ t → a ≤ℝ t → t ≤ℝ b → UniformParameterChange.curve change t ≤ℝ d) where
  private
    module P = UniformComplexPath path
    module T = UniformParameterChange change
    changed : UniformComplexPath a b
    changed = reparameterizeComplexPath path change imageLower imageUpper

  reparameterizedLineIntegrand : ∀ f t → complexLineIntegrand f changed t ≡
    complexLineIntegrand f path (T.curve t) ·ℂ fromℝ (T.velocity t)
  reparameterizedLineIntegrand f t = ·ℂAssoc (f (P.curve (T.curve t))) (P.velocity (T.curve t)) (fromℝ (T.velocity t))

  reparameterizeUniformPrimitive : ∀ F f → IsUniformPrimitiveAlongPath F f path → IsUniformPrimitiveAlongPath F f changed
  reparameterizeUniformPrimitive F f =
    uniformComplexDerivativeAlongPrecompose (ClosedIntervalPremetricSpace a b .snd) (ClosedIntervalPremetricSpace c d .snd)
      (parameterChangeImage path change imageLower imageUpper) (P.curve ∘ fst) (F ∘ P.curve ∘ fst) (f ∘ P.curve ∘ fst)
      (parameterChangeImageIsUniformlyContinuous path change imageLower imageUpper)

  reparameterizeBoundedUniformPrimitive : ∀ F f →
    IsBoundedUniformPrimitiveAlongPath F f path → IsBoundedUniformPrimitiveAlongPath F f changed
  reparameterizeBoundedUniformPrimitive F f (estimate , bounded) = reparameterizeUniformPrimitive F f estimate ,
    PT.map (λ { (B , bound) → B , λ t lo hi → bound (T.curve t) (imageLower t lo hi) (imageUpper t lo hi) }) bounded

  -- These two laws apply to any uniformly continuous line integrand, without
  -- asking the caller for a complex primitive or transformed integrability.
  module _ (f : ℂ → ℂ)
    (continuous : isUniformlyContinuous (ClosedIntervalPremetricSpace c d .snd)
      (complexLineIntegrand f path ∘ fst) (ℂPremetricSpace .snd)) where
    private
      module SubstitutionProof = ComplexSubstitution {a = a} {b = b} {c = c} {d = d}
        (complexLineIntegrand f path) P.ordered continuous change imageLower imageUpper

    reparameterizeHasComplexLineIntegral : T.curve a ≡ c → T.curve b ≡ d → ∀ value →
      HasComplexLineIntegral f path value → HasComplexLineIntegral f changed value
    reparameterizeHasComplexLineIntegral start finish value proof =
      complexHasIntegralCongOn SubstitutionProof.transformed (complexLineIntegrand f changed) a b value
        (λ t lo hi → sym (reparameterizedLineIntegrand f t)) (SubstitutionProof.hasIntegralSameEndpoints start finish value proof)

    reparameterizeSwappedHasComplexLineIntegral : T.curve a ≡ d → T.curve b ≡ c → ∀ value →
      HasComplexLineIntegral f path value → HasComplexLineIntegral f changed (-ℂ value)
    reparameterizeSwappedHasComplexLineIntegral start finish value proof =
      complexHasIntegralCongOn SubstitutionProof.transformed (complexLineIntegrand f changed) a b (-ℂ value)
        (λ t lo hi → sym (reparameterizedLineIntegrand f t)) (SubstitutionProof.hasIntegralSwappedEndpoints start finish value proof)
