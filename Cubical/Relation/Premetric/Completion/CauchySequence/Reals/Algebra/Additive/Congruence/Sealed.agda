module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Congruence.Sealed where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group


opaque
  add-cong₂-sealed : ∀ {a a' b b' : Real.ℝ} →
    a ≡ a' → b ≡ b' → a Add.+ b ≡ a' Add.+ b'
  add-cong₂-sealed a≡a' b≡b' =
    cong₂ Add._+_ a≡a' b≡b'


  sub-cong₂-sealed : ∀ {a a' b b' : Real.ℝ} →
    a ≡ a' → b ≡ b' → a Group.- b ≡ a' Group.- b'
  sub-cong₂-sealed a≡a' b≡b' =
    cong₂ Group._-_ a≡a' b≡b'
