module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Distance where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open OrderedCommRingTheory ℚOrderedCommRing

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Limits


distance : Real.ℝ → Real.ℝ → Real.ℝ
distance x y = Abs.absℝ (x Group.- y)

distance-seqWitness : ∀ {x y} →
  Real.Base.IsCauchySequence x → Real.Base.IsCauchySequence y →
  Real.Base.IsCauchySequence (λ n → distance (x n) (y n))
distance-seqWitness gx gy =
  Abs.absℝ-seqWitness
    (Add.add-diagonalIsCauchySequence gx (Neg.neg-seqWitness gy))

private
  lim-cong : ∀ {x y : ℕ → Real.ℝ}
    (gx : Real.Base.IsCauchySequence x) (gy : Real.Base.IsCauchySequence y) →
    x ≡ y → Real.Base.lim x gx ≡ Real.Base.lim y gy
  lim-cong {x} {y} gx gy p =
    cong (λ z → Real.Base.lim (fst z) (snd z))
      (Σ≡Prop Real.Base.isPropIsCauchySequence p)

  iota-lim-differenceWitness : ∀ p {y} →
    (gy : Real.Base.IsCauchySequence y) →
    Real.Base.IsCauchySequence (λ n → Real.ιℚ p Add.+ (Neg.- y n))
  iota-lim-differenceWitness p gy =
    Add.add-diagonalIsCauchySequence
      (constantIsCauchySequence (Real.ιℚ p)) (Neg.neg-seqWitness gy)

  lim-iota-rationalDifferenceWitness : ∀ {x} →
    (gx : Real.Base.IsCauchySequence x) → ∀ q →
    Real.Base.IsCauchySequence (λ n → x n Add.+ Real.ιℚ (ℚR.- q))
  lim-iota-rationalDifferenceWitness gx q =
    Add.add-diagonalIsCauchySequence gx
      (constantIsCauchySequence (Real.ιℚ (ℚR.- q)))


distance-ι : ∀ p q →
  distance (Real.ιℚ p) (Real.ιℚ q) ≡
  Real.ιℚ (abs (p ℚR.- q))
distance-ι p q =
  cong Abs.absℝ (sub-ι-ι p q) ∙ Abs.absℝ-ι (p ℚR.- q)

distance-ι-lim : ∀ p y gy →
  distance (Real.ιℚ p) (Real.Base.lim y gy) ≡
  Real.Base.lim (λ n → distance (Real.ιℚ p) (y n))
    (distance-seqWitness (constantIsCauchySequence (Real.ιℚ p)) gy)
distance-ι-lim p y gy =
    cong Abs.absℝ
      (cong (Real.ιℚ p Add.+_) (Neg.neg-lim y gy))
  ∙ cong Abs.absℝ
      (Add.add-ι-lim p (Neg.-_ ∘ y) (Neg.neg-seqWitness gy)
      ∙ lim-cong _ (iota-lim-differenceWitness p gy) refl)
  ∙ Abs.absℝ-lim
      (λ n → Real.ιℚ p Add.+ (Neg.- y n))
      (iota-lim-differenceWitness p gy)

distance-lim-ι : ∀ x gx q →
  distance (Real.Base.lim x gx) (Real.ιℚ q) ≡
  Real.Base.lim (λ n → distance (x n) (Real.ιℚ q))
    (distance-seqWitness gx (constantIsCauchySequence (Real.ιℚ q)))
distance-lim-ι x gx q =
    cong Abs.absℝ
      (cong (Real.Base.lim x gx Add.+_) (Neg.neg-ι q))
  ∙ cong Abs.absℝ
      (Add.add-lim-ι x gx (ℚR.- q)
      ∙ lim-cong _ (lim-iota-rationalDifferenceWitness gx q) refl)
  ∙ Abs.absℝ-lim (λ n → x n Add.+ Real.ιℚ (ℚR.- q))
      (lim-iota-rationalDifferenceWitness gx q)
  ∙ lim-cong _ (distance-seqWitness gx (constantIsCauchySequence (Real.ιℚ q)))
      (funExt λ n →
      cong Abs.absℝ
        (cong (x n Add.+_) (sym (Neg.neg-ι q))))

distance-lim-lim : ∀ x gx y gy →
  distance (Real.Base.lim x gx) (Real.Base.lim y gy) ≡
  Real.Base.lim (λ n → distance (x n) (y n))
    (distance-seqWitness gx gy)
distance-lim-lim x gx y gy =
    absDifference-lim-lim x gx y gy
  ∙ lim-cong _ (distance-seqWitness gx gy) refl

distance-refl : ∀ x → distance x x ≡ Real.ιℚ 0
distance-refl x =
  cong Abs.absℝ (sub-self x) ∙ Abs.absℝ-zero

distance-sym : ∀ x y → distance x y ≡ distance y x
distance-sym x y =
    sym (Abs.absℝ-neg (x Group.- y))
  ∙ cong Abs.absℝ (neg-sub x y)


private
  telescoping-difference : ∀ x y z →
    (x Group.- y) Add.+ (y Group.- z) ≡ x Group.- z
  telescoping-difference x y z =
      sym (add-assoc x (Neg.- y) (y Add.+ (Neg.- z)))
    ∙ cong (x Add.+_)
        (add-assoc (Neg.- y) y (Neg.- z)
        ∙ cong (Add._+ (Neg.- z)) (add-inverse-left y)
        ∙ add-zero-left (Neg.- z))


distance-triangle : ∀ x y z →
  distance x z ≤ℝ
  (distance x y Add.+ distance y z)
distance-triangle x y z =
  subst (_≤ℝ (distance x y Add.+ distance y z))
    (cong Abs.absℝ (telescoping-difference x y z))
    (abs-triangle (x Group.- y) (y Group.- z))

distance-eq-zero→eq : ∀ x y →
  distance x y ≡ Real.ιℚ 0 → x ≡ y
distance-eq-zero→eq x y distance≡0 =
    sym (sub-add-cancel x y)
  ∙ cong (Add._+ y)
      (abs-eq-zero→eq-zero (x Group.- y) distance≡0)
  ∙ add-zero-left y

eq→distance-eq-zero : ∀ x y →
  x ≡ y → distance x y ≡ Real.ιℚ 0
eq→distance-eq-zero x y x≡y =
  sym (cong (distance x) x≡y) ∙ distance-refl x
