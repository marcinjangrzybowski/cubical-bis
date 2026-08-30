module Cubical.Relation.Premetric.Completion.UniversalProperty.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Base

open PositiveRationals


-- Construction-independent data presented by a completion: an isometric
-- dense embedding into a completed premetric space.  No constructors or
-- elimination principles of the completed carrier occur in this record.

record CompletionPresentation
  {ℓM ℓM'} (M' : PremetricSpace ℓM ℓM')
  (ℓC ℓC' : Level) :
  Type (ℓ-suc (ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓC ℓC'))) where

  no-eta-equality
  constructor completionPresentation

  private
    module M = PremetricStr (M' .snd)

  field
    completionSpace : PremetricSpace ℓC ℓC'
    injection : M' .fst → completionSpace .fst

  private
    module C = PremetricStr (completionSpace .snd)

  field
    injection-pres≈ : ∀ x y ε →
      (x M.≈[ ε ] y) ≃
      (injection x C.≈[ ε ] injection y)

    dense : ∀ x ε →
      ∃[ q ∈ M' .fst ] (injection q C.≈[ ε ] x)

open CompletionPresentation public
