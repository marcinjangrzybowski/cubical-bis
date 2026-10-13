module Cubical.Analysis.Complex.Integration.LineIntegral.Translation where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Integration.Base
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Translation
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base

-- Translation covariance is an identity of the actual integrands: the
-- translated curve has exactly the original velocity.
translateHasComplexLineIntegral : ∀ {a b} (path : UniformComplexPath a b) offset f value →
  HasComplexLineIntegral (λ z → f (z +ℂ offset)) path value →
  HasComplexLineIntegral f (translateComplexPath path offset) value
translateHasComplexLineIntegral path offset f value proof = proof

recenterHasComplexLineIntegral : ∀ {a b} (path : UniformComplexPath a b) center f value →
  HasComplexLineIntegral (λ z → f (z +ℂ center)) (recenterComplexPath path center) value →
  HasComplexLineIntegral f path value
recenterHasComplexLineIntegral {a} {b} path center f value = complexHasIntegralCongOn
  (complexLineIntegrand (λ z → f (z +ℂ center)) (recenterComplexPath path center))
  (complexLineIntegrand f path) a b value
  (λ t _ _ → cong (λ z → f z ·ℂ UniformComplexPath.velocity path t)
    (ℂRing.minusPlus (UniformComplexPath.curve path t) center))
