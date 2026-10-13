module Cubical.Analysis.Complex.Inverse.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order using (positiveReciprocalPositive)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Multiplication using (mulPositive)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Inverse
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds

opaque
  -- An explicit multiplicative inverse gives positive apartness, not
  -- merely a proof that the value cannot equal zero.
  unit→modulusPositiveℂ : ∀ z w → z ·ℂ w ≡ 1ℂ → 0ℝ <ℝ modulusℂ z
  unit→modulusPositiveℂ z w unit = <≤ℝ-trans 0ℝ reciprocal (modulusℂ z)
    (positiveReciprocalPositive bound bound-positive) reciprocal-lower
    where
    bound : ℝ
    bound = modulusℂ w + 1ℝ
    bound-positive : 0ℝ <ℝ bound
    bound-positive = subst (_<ℝ bound) (addIdR 0ℝ)
      (≤<ℝ-add 0ℝ (modulusℂ w) 0ℝ 1ℝ (modulusℂ-nonnegative w) (<ℚ→<ℝ 0 1 (ℚ.pos<pos tt)))
    reciprocal : ℝ
    reciprocal = positiveReciprocal bound bound-positive
    w-bounded : modulusℂ w ≤ℝ bound
    w-bounded = subst (_≤ℝ bound) (addIdR (modulusℂ w))
      (addPres≤L 0ℝ 1ℝ (modulusℂ w) (<ℝ-weaken 0ℝ 1ℝ (<ℚ→<ℝ 0 1 (ℚ.pos<pos tt))))
    product-bound : 1ℝ ≤ℝ modulusℂ z · bound
    product-bound = subst (_≤ℝ modulusℂ z · bound)
      (sym (modulusℂ-mul z w) ∙ cong modulusℂ unit ∙ modulusℂ-one)
      (mulPres≤L (modulusℂ w) bound (modulusℂ z) (0≤→isNonnegative (modulusℂ z) (modulusℂ-nonnegative z)) w-bounded)
    cancel : (modulusℂ z · bound) · reciprocal ≡ modulusℂ z
    cancel = sym (mulAssoc (modulusℂ z) bound reciprocal)
      ∙ cong (modulusℂ z ·_) (positiveReciprocalLaw bound bound-positive) ∙ mulIdR (modulusℂ z)
    reciprocal-lower : reciprocal ≤ℝ modulusℂ z
    reciprocal-lower = subst2 _≤ℝ_ (mulIdL reciprocal) cancel
      (mulPres≤R-0≤ 1ℝ (modulusℂ z · bound) reciprocal
        (<ℝ-weaken 0ℝ reciprocal (positiveReciprocalPositive bound bound-positive)) product-bound)

  modulusPositive→nonzeroℂ : ∀ z → 0ℝ <ℝ modulusℂ z → ComplexNonzero z
  modulusPositive→nonzeroℂ z positive = subst (0ℝ <ℝ_) (modulusℂ-square z)
    (mulPositive (modulusℂ z) (modulusℂ z) positive positive)

  -- The lower bound is independent of the particular apartness proof.
  -- This is useful when a Bézout certificate bounds a derivative uniformly.
  inverseℂ-modulusBound : ∀ z (nonzero : ComplexNonzero z) lower
    (positive : 0ℝ <ℝ lower) → lower ≤ℝ modulusℂ z →
    modulusℂ (inverseℂ z nonzero) ≤ℝ positiveReciprocal lower positive
  inverseℂ-modulusBound z nonzero lower positive bounded =
    subst2 _≤ℝ_ cancel (mulIdR reciprocal)
      (mulPres≤L (lower · modulusℂ inverse) 1ℝ reciprocal
        (0≤→isNonnegative reciprocal (<ℝ-weaken 0ℝ reciprocal (positiveReciprocalPositive lower positive)))
        (subst (lower · modulusℂ inverse ≤ℝ_)
          (sym (modulusℂ-mul z inverse) ∙ cong modulusℂ (inverseℂ-law z nonzero) ∙ modulusℂ-one)
          (mulPres≤R-0≤ lower (modulusℂ z) (modulusℂ inverse) (modulusℂ-nonnegative inverse) bounded)))
    where
    inverse : ℂ
    inverse = inverseℂ z nonzero
    reciprocal : ℝ
    reciprocal = positiveReciprocal lower positive
    cancel : reciprocal · (lower · modulusℂ inverse) ≡ modulusℂ inverse
    cancel = mulAssoc reciprocal lower (modulusℂ inverse)
      ∙ cong (_· modulusℂ inverse) (positiveReciprocalLaw' lower positive)
      ∙ mulIdL (modulusℂ inverse)

  inverseℂ-normBound : ∀ z (nonzero : ComplexNonzero z) lower
    (positive : 0ℝ <ℝ lower) → lower ≤ℝ modulusℂ z →
    normℂ (inverseℂ z nonzero) ≤ℝ
      positiveReciprocal lower positive + positiveReciprocal lower positive
  inverseℂ-normBound z nonzero lower positive bounded =
    ≤ℝ-trans (normℂ inverse) (modulusℂ inverse + modulusℂ inverse) (reciprocal + reciprocal)
      (normℂ≤twiceModulusℂ inverse)
      (addPres≤ (modulusℂ inverse) reciprocal (modulusℂ inverse) reciprocal
        (inverseℂ-modulusBound z nonzero lower positive bounded)
        (inverseℂ-modulusBound z nonzero lower positive bounded))
    where
    inverse : ℂ
    inverse = inverseℂ z nonzero
    reciprocal : ℝ
    reciprocal = positiveReciprocal lower positive
