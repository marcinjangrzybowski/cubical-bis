module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Rationals.Order.Floor
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open OrderedCommRingTheory ℚOrderedCommRing

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Density


-- An absolute-value bound contains only one finite rational choice.  This is
-- the form needed by local arguments such as multiplication and reciprocal;
-- no modulus or countable family of bounds is selected.

RationalBound : Real.ℝ → Type
RationalBound x =
  Σ[ B ∈ ℚ₊ ] Abs.absℝ x ≤ℝ Real.ιℚ (fst B)


isPropRationalBound : ∀ x → isProp (∥ RationalBound x ∥₁)
isPropRationalBound _ = squash₁


private
  onePositive : 0 ℚ.< 1
  onePositive = OrderedCommRingStr.0<1 (snd ℚOrderedCommRing)

  absBelowAbsPlusOne : ∀ x →
    Abs.absℝ x <ℝ
      (Abs.absℝ x Add.+ Real.ιℚ 1)
  absBelowAbsPlusOne x =
    subst
      (λ z → z <ℝ (Abs.absℝ x Add.+ Real.ιℚ 1))
      (add-zero-right (Abs.absℝ x))
      (<ℝ-add-left
        (Real.ιℚ 0) (Real.ιℚ 1) (Abs.absℝ x)
        (<ℚ→<ℝ 0 1 onePositive))

  rationalUpper→AbsBound : ∀ x →
    (Σ[ q ∈ ℚ ]
      (Abs.absℝ x <ℝ Real.ιℚ q) ×
      (Real.ιℚ q <ℝ
        (Abs.absℝ x Add.+ Real.ιℚ 1))) →
    RationalBound x
  rationalUpper→AbsBound x (q , absx≪q , _) =
    (q , qPositive)
    , <ℝ-weaken (Abs.absℝ x) (Real.ιℚ q) absx≪q
    where
    zero≪q : Real.ιℚ 0 <ℝ Real.ιℚ q
    zero≪q = ≤<ℝ-trans
      (Real.ιℚ 0) (Abs.absℝ x) (Real.ιℚ q)
      (zero≤abs x) absx≪q

    qPositive : 0 ℚ.< q
    qPositive = <ℝ→<ℚ 0 q zero≪q


∃rationalBound : ∀ x → ∥ RationalBound x ∥₁
∃rationalBound x =
  PT.map (rationalUpper→AbsBound x)
    (denseℚinℝ
      (Abs.absℝ x)
      (Abs.absℝ x Add.+ Real.ιℚ 1)
      (absBelowAbsPlusOne x))


JointRationalBound : Real.ℝ → Real.ℝ → Type
JointRationalBound x y =
  Σ[ B ∈ ℚ₊ ]
    (Abs.absℝ x ≤ℝ Real.ιℚ (fst B)) ×
    (Abs.absℝ y ≤ℝ Real.ιℚ (fst B))


∃jointRationalBound : ∀ x y → ∥ JointRationalBound x y ∥₁
∃jointRationalBound x y = PT.map2 combine (∃rationalBound x) (∃rationalBound y)
  where
  combine : RationalBound x → RationalBound y → JointRationalBound x y
  combine (B , absx≤B) (C , absy≤C) =
    max₊ B C
    , ≤ℝ-trans
        (Abs.absℝ x) (Real.ιℚ (fst B)) (Real.ιℚ (fst (max₊ B C)))
        absx≤B
        (≤ℚ→≤ℝ (fst B) (fst (max₊ B C))
          (ℚ.≤max (fst B) (fst C)))
    , ≤ℝ-trans
        (Abs.absℝ y) (Real.ιℚ (fst C)) (Real.ιℚ (fst (max₊ B C)))
        absy≤C
        (≤ℚ→≤ℝ (fst C) (fst (max₊ B C))
          (ℚ.≤max' (fst B) (fst C)))


naturalRational : ℕ₊₁ → ℚ
naturalRational n = [ ℤ.ℕ₊₁→ℤ n , 1 ]


naturalPositive : ∀ n → 0 ℚ.< naturalRational n
naturalPositive (1+ n) = 0<pos n 1


NaturalBound : Real.ℝ → Type
NaturalBound x =
  Σ[ n ∈ ℕ₊₁ ] Abs.absℝ x <ℝ Real.ιℚ (naturalRational n)


∃naturalBound : ∀ x → ∥ NaturalBound x ∥₁
∃naturalBound x = PT.map toNatural (∃rationalBound x)
  where
  toNatural : RationalBound x → NaturalBound x
  toNatural (B , absx≤B) =
    n
    , ≤<ℝ-trans
        (Abs.absℝ x) (Real.ιℚ (fst B))
        (Real.ιℚ (naturalRational n))
        absx≤B
        (<ℚ→<ℝ (fst B) (naturalRational n) B<n)
    where
    n : ℕ₊₁
    n = fst (boundℕ (fst B))

    absB<n : abs (fst B) ℚ.< naturalRational n
    absB<n = snd (boundℕ (fst B))

    B<n : fst B ℚ.< naturalRational n
    B<n = ℚ.isTrans≤<
      (fst B) (abs (fst B)) (naturalRational n)
      (≤abs (fst B)) absB<n
