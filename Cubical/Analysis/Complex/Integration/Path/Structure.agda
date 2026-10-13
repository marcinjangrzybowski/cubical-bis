module Cubical.Analysis.Complex.Integration.Path.Structure where

open import Cubical.Foundations.Prelude

-- Keep the predicates abstract while Agda generates the record operations.
-- Instantiating afterwards avoids normalizing native real order/derivative
-- predicates during generation of the cubical composition structure.
module PathStructure (Parameter Value Bound : Type₀)
  (Ordered : Parameter → Parameter → Type₀)
  (HasDerivative : (Parameter → Value) → (Parameter → Value) → Parameter → Parameter → Type₀)
  (Bounded : (Parameter → Value) → Parameter → Parameter → Bound → Type₀) where

  record UniformPath (a b : Parameter) : Type₀ where
    field
      ordered : Ordered a b
      curve velocity : Parameter → Value
      differentiable : HasDerivative curve velocity a b
      speedBound : Bound
      boundedSpeed : Bounded velocity a b speedBound
