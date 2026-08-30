module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra.Sealed where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra


opaque
  addHasDerivative-sealed : ∀ f g f' g' →
    IsDerivative f f' → IsDerivative g g' →
    IsDerivative
      (λ x → f x Add.+ g x)
      (λ x → f' x Add.+ g' x)
  addHasDerivative-sealed = addHasDerivative


  subHasDerivative-sealed : ∀ f g f' g' →
    IsDerivative f f' → IsDerivative g g' →
    IsDerivative
      (λ x → f x Group.- g x)
      (λ x → f' x Group.- g' x)
  subHasDerivative-sealed = subHasDerivative


  scaleHasDerivative-sealed : ∀ f f' c →
    IsDerivative f f' →
    IsDerivative
      (λ x → c Mul.· f x)
      (λ x → c Mul.· f' x)
  scaleHasDerivative-sealed = scaleHasDerivative
