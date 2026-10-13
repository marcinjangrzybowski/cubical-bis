module Cubical.Analysis.Complex.Integration.LineIntegral.Reversal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Reversal
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.Bounded
open import Cubical.Analysis.Complex.Integration.LineIntegral.Reparameterization
import Cubical.Analysis.Complex.Modulus.DistanceAlgebra as Algebra

private module C = Algebra.DistanceAlgebra ℂCommRing

reverseHasComplexLineIntegral : ∀ {a b} (path : UniformComplexPath a b) f →
  isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (complexLineIntegrand f path ∘ fst) (ℂPremetricSpace .snd) →
  ∀ value → HasComplexLineIntegral f path value → HasComplexLineIntegral f (reverseComplexPath path) (-ℂ value)
reverseHasComplexLineIntegral {a} {b} path f continuous =
  reparameterizeSwappedHasComplexLineIntegral path (reflectUniformParameterChange a b (UniformComplexPath.ordered path))
    (reflectParameterLower a b) (reflectParameterUpper a b) f continuous (reflectParameterAtStart a b) (reflectParameterAtFinish a b)

reverseBoundedUniformPrimitive : ∀ {a b} (path : UniformComplexPath a b) F f →
  IsBoundedUniformPrimitiveAlongPath F f path → IsBoundedUniformPrimitiveAlongPath F f (reverseComplexPath path)
reverseBoundedUniformPrimitive {a} {b} path =
  reparameterizeBoundedUniformPrimitive path (reflectUniformParameterChange a b (UniformComplexPath.ordered path))
    (reflectParameterLower a b) (reflectParameterUpper a b)

-- For supplied uniform primitives, reversal needs no standard continuity
-- modulus for the line integrand; the radiuswise FTC suffices.
reversePrimitiveHasComplexLineIntegral : ∀ {a b} (path : UniformComplexPath a b) F f →
  IsBoundedUniformPrimitiveAlongPath F f path → ∀ value → HasComplexLineIntegral f path value →
  HasComplexLineIntegral f (reverseComplexPath path) (-ℂ value)
reversePrimitiveHasComplexLineIntegral path F f estimate value proof =
  subst (HasComplexLineIntegral f (reverseComplexPath path))
    (cong₂ _-ℂ_ (cong F (reverseComplexPathFinishesAtStart path)) (cong F (reverseComplexPathStartsAtFinish path))
      ∙ C.difference-opposite (F (pathStart path)) (F (pathFinish path))
      ∙ cong -ℂ_ (sym (complexLineIntegralUnique f path value (F (pathFinish path) -ℂ F (pathStart path)) proof
        (boundedUniformPrimitiveHasComplexLineIntegral path F f estimate))))
    (boundedUniformPrimitiveHasComplexLineIntegral (reverseComplexPath path) F f (reverseBoundedUniformPrimitive path F f estimate))
