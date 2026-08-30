module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Positive.Global where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum using (inl)

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (neg-x≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Multiplication
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Addition.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Positive.NonnegativeNegation


-- This is the sign-free decomposition used below.  Its first summand is
-- nonnegative in the lattice order, while the absolute value itself is
-- nonnegative, so neither a comparison with zero nor excluded middle is
-- needed.

zero≤self-plus-absolute : ∀ x →
  zeroℝ ≤ℝ (x Add.+ Abs.absℝ x)
zero≤self-plus-absolute x =
  subst2 _≤ℝ_
    (add-inverse-right x) refl
    (add-preserves≤-left
      (Neg.- x) (Abs.absℝ x) x (neg-x≤abs x))


self-plus-absolute-minus-absolute : ∀ x →
  (x Add.+ Abs.absℝ x) Add.+ (Neg.- Abs.absℝ x) ≡ x
self-plus-absolute-minus-absolute x =
    sym (add-assoc x (Abs.absℝ x) (Neg.- Abs.absℝ x))
  ∙ cong (x Add.+_) (add-inverse-right (Abs.absℝ x))
  ∙ add-zero-right x


-- Positivity is global.  The proof uses the completion's lattice absolute
-- value to replace a nonconstructive sign split by the canonical
-- decomposition x = (x + |x|) + (-|x|).

-- Positivity proofs occur as explicit arguments to the constructive
-- reciprocal.  Sealing this proof prevents those arguments from unfolding
-- the whole absolute-value decomposition during downstream conversion.
opaque
  expℝ-positive : ∀ x → zeroℝ <ℝ expℝ x
  expℝ-positive x =
    subst (zeroℝ <ℝ_)
      (sym exponential-decomposition)
      (mul-positive
        (expℝ (x Add.+ Abs.absℝ x))
        (expℝ (Neg.- Abs.absℝ x))
        (expℝPositiveOfNonnegative
          (x Add.+ Abs.absℝ x)
          (zero≤self-plus-absolute x))
        (expℝ-neg-positiveOfNonnegative
          (Abs.absℝ x) (zero≤abs x)))
    where
    exponential-decomposition :
      expℝ x ≡
      expℝ (x Add.+ Abs.absℝ x) Mul.·
        expℝ (Neg.- Abs.absℝ x)
    exponential-decomposition =
        expℝ-cong-sealed (sym (self-plus-absolute-minus-absolute x))
      ∙ expℝ-add-sealed
          (x Add.+ Abs.absℝ x) (Neg.- Abs.absℝ x)


  expℝ-apart-zero : ∀ x → zeroℝ ＃ expℝ x
  expℝ-apart-zero x = inl (expℝ-positive x)
