module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Sum.Close where

open import Cubical.Foundations.Prelude

import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Data.Rationals.Inverse

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (x≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (mul-preserves≤-right-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (_<ℝ_ ; ≤<ℝ-trans ; <ℚ→<ℝ ; <ℝ-weaken)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (closeness→absDifference< ; absDifference<→closeness)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannSum.DyadicRecursive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Sum.AbsBound


-- A rational width bound converts the real-valued operator estimate into a
-- metric estimate.  The same radius works at every dyadic depth.

dyadicRecursiveSum-pointwiseClose :
  ∀ f g a b ε B n →
  Abs.absℝ (b Group.- a) ≤ℝ Real.ιℚ (fst B) →
  (a≤b : a ≤ℝ b) →
  (∀ x → a ≤ℝ x → x ≤ℝ b →
    f x Real.Base.≈ᶜ[ (((ε /2₊) /2₊) ₊／₊ B) ] g x) →
  dyadicRecursiveSum f a b n Real.Base.≈ᶜ[ ε /2₊ ]
  dyadicRecursiveSum g a b n
dyadicRecursiveSum-pointwiseClose
  f g a b ε B n width-bound a≤b pointwise =
  absDifference<→closeness
    (dyadicRecursiveSum f a b n)
    (dyadicRecursiveSum g a b n) (ε /2₊)
    (≤<ℝ-trans
      (Abs.absℝ
        (dyadicRecursiveSum f a b n Group.-
          dyadicRecursiveSum g a b n))
      ((b Group.- a) Mul.· Real.ιℚ (fst input-radius))
      (Real.ιℚ (fst (ε /2₊)))
      (dyadicRecursiveSum-pointwiseAbsBound
        f g a b (Real.ιℚ (fst input-radius)) n a≤b
        (λ x a≤x x≤b →
          <ℝ-weaken _ _
            (closeness→absDifference<
              (f x) (g x) input-radius (pointwise x a≤x x≤b))))
      product-small)
  where
  quarter-radius : ℚ₊
  quarter-radius = (ε /2₊) /2₊

  input-radius : ℚ₊
  input-radius = quarter-radius ₊／₊ B

  width≤B : b Group.- a ≤ℝ Real.ιℚ (fst B)
  width≤B =
    ≤ℝ-trans
      (b Group.- a) (Abs.absℝ (b Group.- a))
      (Real.ιℚ (fst B))
      (x≤abs (b Group.- a)) width-bound

  zero≤input : Real.ιℚ 0 ≤ℝ Real.ιℚ (fst input-radius)
  zero≤input =
    ≤ℚ→≤ℝ 0 (fst input-radius)
      (ℚ.<Weaken≤ 0 (fst input-radius) (snd input-radius))

  product-upper :
    (b Group.- a) Mul.· Real.ιℚ (fst input-radius) ≤ℝ
    Real.ιℚ (fst B) Mul.· Real.ιℚ (fst input-radius)
  product-upper =
    mul-preserves≤-right-nonnegative
      (b Group.- a) (Real.ιℚ (fst B))
      (Real.ιℚ (fst input-radius)) width≤B zero≤input

  rational-product :
    Real.ιℚ (fst B) Mul.· Real.ιℚ (fst input-radius) ≡
    Real.ιℚ (fst quarter-radius)
  rational-product =
    Mul.mul-ι-ι (fst B) (fst input-radius)
    ∙ cong Real.ιℚ (·／ B quarter-radius)

  product-small :
    (b Group.- a) Mul.· Real.ιℚ (fst input-radius) <ℝ
    Real.ιℚ (fst (ε /2₊))
  product-small =
    ≤<ℝ-trans
      ((b Group.- a) Mul.· Real.ιℚ (fst input-radius))
      (Real.ιℚ (fst B) Mul.· Real.ιℚ (fst input-radius))
      (Real.ιℚ (fst (ε /2₊)))
      product-upper
      (subst (_<ℝ Real.ιℚ (fst (ε /2₊)))
        (sym rational-product)
        (<ℚ→<ℝ
          (fst quarter-radius) (fst (ε /2₊))
          (/2₊<id (ε /2₊))))
