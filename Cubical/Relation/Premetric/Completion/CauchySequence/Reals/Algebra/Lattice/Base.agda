module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat.Base using (ℕ)

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.NatPlusOne
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base
  as Scalar
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Laws

open OrderedCommRingTheory ℚOrderedCommRing
open PositiveRationals
open 1/2∈ℚ


rationalHalf : ℚ
rationalHalf = fst [ 1 / 2 ]₊

rationalMaxFormula : ∀ p q →
  rationalHalf ℚR.· ((p ℚR.+ q) ℚR.+ abs (p ℚR.- q)) ≡
  ℚ.max p q
rationalMaxFormula = elimBy≤ swap ordered
    where
    ordered : ∀ p q → p ℚ.≤ q →
      rationalHalf ℚR.· ((p ℚR.+ q) ℚR.+ abs (p ℚR.- q)) ≡
      ℚ.max p q
    ordered p q p≤q =
        cong (λ z → rationalHalf ℚR.· ((p ℚR.+ q) ℚR.+ z))
          (≤0→abs≡- (p ℚR.- q)
            (subst (p ℚR.- q ℚ.≤_) (ℚR.+InvR q)
              (ℚ.≤-+o p q (ℚR.- q) p≤q)))
      ∙ ℚ!
      ∙ sym (ℚ.≤→max p q p≤q)

    swap : ∀ p q →
      rationalHalf ℚR.· ((p ℚR.+ q) ℚR.+ abs (p ℚR.- q)) ≡
        ℚ.max p q →
      rationalHalf ℚR.· ((q ℚR.+ p) ℚR.+ abs (q ℚR.- p)) ≡
        ℚ.max q p
    swap p q IH =
        cong (λ z → rationalHalf ℚR.· ((q ℚR.+ p) ℚR.+ z))
          (abs-Comm q p)
      ∙ cong (λ z → rationalHalf ℚR.· (z ℚR.+ abs (p ℚR.- q)))
          (ℚR.+Comm q p)
      ∙ IH
      ∙ ℚ.maxComm p q


infixl 7 _⊔ℝ_ _⊓ℝ_

_⊔ℝ_ : Real.ℝ → Real.ℝ → Real.ℝ
x ⊔ℝ y =
  rationalHalf Scalar.⋆
    ((x Add.+ y) Add.+ Abs.absℝ (x Group.- y))

_⊓ℝ_ : Real.ℝ → Real.ℝ → Real.ℝ
x ⊓ℝ y = Neg.- ((Neg.- x) ⊔ℝ (Neg.- y))


max-ι : ∀ p q →
  Real.ιℚ p ⊔ℝ Real.ιℚ q ≡ Real.ιℚ (ℚ.max p q)
max-ι p q =
  cong (rationalHalf Scalar.⋆_)
    (cong₂ Add._+_
      (Add.add-ι-ι p q)
      (cong Abs.absℝ (sub-ι-ι p q)
        ∙ Abs.absℝ-ι (p ℚR.- q))
    ∙ Add.add-ι-ι (p ℚR.+ q) (abs (p ℚR.- q)))
  ∙ Scalar.scalar-ι rationalHalf
      ((p ℚR.+ q) ℚR.+ abs (p ℚR.- q))
  ∙ cong Real.ιℚ (rationalMaxFormula p q)

-- The formula advances the two sequences synchronously.  This follows
-- from the synchronized computation rule for addition and the unary
-- computation rules for absolute value and rational scaling.

max-lim-left : ∀ x gx y →
  Real.Base.lim x gx ⊔ℝ y ≡
  Real.Base.lim (λ n → x n ⊔ℝ y) _
max-lim-left x gx y =
  cong (rationalHalf Scalar.⋆_)
    (Add.add-lim-lim
      (λ n → x n Add.+ y) _
      (λ n → Abs.absℝ (x n Group.- y)) _)

private
  sum-seqWitness : ∀ {x y} →
    Real.Base.IsCauchySequence x → Real.Base.IsCauchySequence y →
    Real.Base.IsCauchySequence (λ n → x n Add.+ y n)
  sum-seqWitness = Add.add-diagonalIsCauchySequence

  difference-seqWitness : ∀ {x y} →
    Real.Base.IsCauchySequence x → Real.Base.IsCauchySequence y →
    Real.Base.IsCauchySequence (λ n → x n Group.- y n)
  difference-seqWitness gx gy =
    Add.add-diagonalIsCauchySequence gx (Neg.neg-seqWitness gy)

  absDifference-seqWitness : ∀ {x y} →
    (gx : Real.Base.IsCauchySequence x) (gy : Real.Base.IsCauchySequence y) →
    Real.Base.IsCauchySequence (λ n → Abs.absℝ (x n Group.- y n))
  absDifference-seqWitness gx gy =
    Abs.absℝ-seqWitness (difference-seqWitness gx gy)

  maxBody-seqWitness : ∀ {x y} →
    (gx : Real.Base.IsCauchySequence x) (gy : Real.Base.IsCauchySequence y) →
    Real.Base.IsCauchySequence (λ n →
      (x n Add.+ y n) Add.+ Abs.absℝ (x n Group.- y n))
  maxBody-seqWitness gx gy =
    Add.add-diagonalIsCauchySequence
      (sum-seqWitness gx gy) (absDifference-seqWitness gx gy)

  sumLimit : ∀ (x : ℕ → Real.ℝ) (gx : Real.Base.IsCauchySequence x)
    (y : ℕ → Real.ℝ) (gy : Real.Base.IsCauchySequence y) → Real.ℝ
  sumLimit x gx y gy =
    Real.Base.lim (λ n → x n Add.+ y n) (sum-seqWitness gx gy)

  differenceLimit : ∀ (x : ℕ → Real.ℝ) (gx : Real.Base.IsCauchySequence x)
    (y : ℕ → Real.ℝ) (gy : Real.Base.IsCauchySequence y) → Real.ℝ
  differenceLimit x gx y gy =
    Real.Base.lim (λ n → x n Group.- y n)
      (difference-seqWitness gx gy)

  absDifferenceLimit : ∀ (x : ℕ → Real.ℝ)
    (gx : Real.Base.IsCauchySequence x) (y : ℕ → Real.ℝ)
    (gy : Real.Base.IsCauchySequence y) → Real.ℝ
  absDifferenceLimit x gx y gy =
    Real.Base.lim (λ n → Abs.absℝ (x n Group.- y n))
      (absDifference-seqWitness gx gy)


opaque
 sum-lim-lim : ∀ x gx y gy →
   Real.Base.lim x gx Add.+ Real.Base.lim y gy ≡ sumLimit x gx y gy
 sum-lim-lim = Add.add-lim-lim

 difference-lim-lim : ∀ x gx y gy →
   Real.Base.lim x gx Group.- Real.Base.lim y gy ≡
   differenceLimit x gx y gy
 difference-lim-lim x gx y gy =
   Add.add-lim-lim x gx (Neg.-_ ∘ y) (Neg.neg-seqWitness gy)

 absDifference-lim-lim : ∀ x gx y gy →
   Abs.absℝ (Real.Base.lim x gx Group.- Real.Base.lim y gy) ≡
   absDifferenceLimit x gx y gy
 absDifference-lim-lim x gx y gy =
   cong Abs.absℝ (difference-lim-lim x gx y gy)


max-diagonalIsCauchySequence : ∀ {x y} →
  (gx : Real.Base.IsCauchySequence x) (gy : Real.Base.IsCauchySequence y) →
  Real.Base.IsCauchySequence (λ n → x n ⊔ℝ y n)
max-diagonalIsCauchySequence gx gy =
  Scalar.scalar-seqWitness rationalHalf (maxBody-seqWitness gx gy)


opaque
 maxBody-lim-lim : ∀ x gx y gy →
   ((Real.Base.lim x gx Add.+ Real.Base.lim y gy) Add.+
     Abs.absℝ (Real.Base.lim x gx Group.- Real.Base.lim y gy)) ≡
   Real.Base.lim
     (λ n → (x n Add.+ y n) Add.+
       Abs.absℝ (x n Group.- y n))
     (maxBody-seqWitness gx gy)
 maxBody-lim-lim x gx y gy =
     cong (Add._+ Abs.absℝ
       (Real.Base.lim x gx Group.- Real.Base.lim y gy))
       (sum-lim-lim x gx y gy)
   ∙ cong (sumLimit x gx y gy Add.+_)
       (absDifference-lim-lim x gx y gy)
   ∙ Add.add-lim-lim
       (λ n → x n Add.+ y n) (sum-seqWitness gx gy)
       (λ n → Abs.absℝ (x n Group.- y n))
       (absDifference-seqWitness gx gy)

max-lim-lim : ∀ x gx y gy →
  Real.Base.lim x gx ⊔ℝ Real.Base.lim y gy ≡
  Real.Base.lim (λ n → x n ⊔ℝ y n)
    (max-diagonalIsCauchySequence gx gy)
max-lim-lim x gx y gy =
  cong (rationalHalf Scalar.⋆_) (maxBody-lim-lim x gx y gy)

min-ι : ∀ p q →
  Real.ιℚ p ⊓ℝ Real.ιℚ q ≡ Real.ιℚ (ℚ.min p q)
min-ι p q =
    cong Neg.-_
      (cong₂ _⊔ℝ_ (Neg.neg-ι p) (Neg.neg-ι q))
  ∙ cong Neg.-_ (max-ι (ℚR.- p) (ℚR.- q))
  ∙ Neg.neg-ι (ℚ.max (ℚR.- p) (ℚR.- q))
  ∙ cong Real.ιℚ
      (cong ℚR.-_ (ℚ.maxNeg≡negMin p q)
      ∙ ℚ.-Invol (ℚ.min p q))


private
  abs-sub-comm : ∀ x y →
    Abs.absℝ (x Group.- y) ≡ Abs.absℝ (y Group.- x)
  abs-sub-comm x y =
    sym (Abs.absℝ-neg (x Group.- y))
    ∙ cong Abs.absℝ (neg-sub x y)

max-comm : ∀ x y → x ⊔ℝ y ≡ y ⊔ℝ x
max-comm x y =
  cong (rationalHalf Scalar.⋆_)
    (cong₂ Add._+_
      (add-comm x y)
      (abs-sub-comm x y))

min-comm : ∀ x y → x ⊓ℝ y ≡ y ⊓ℝ x
min-comm x y = cong Neg.-_ (max-comm (Neg.- x) (Neg.- y))


private
  double-as-two-scalar : ∀ x →
    x Add.+ x ≡ (1 ℚR.+ 1) Scalar.⋆ x
  double-as-two-scalar x =
    cong₂ Add._+_ (sym (scalar-id x)) (sym (scalar-id x))
    ∙ sym (scalar-dist-left 1 1 x)

max-idempotent : ∀ x → x ⊔ℝ x ≡ x
max-idempotent x =
    cong (rationalHalf Scalar.⋆_)
      (cong ((x Add.+ x) Add.+_)
        (cong Abs.absℝ (sub-self x) ∙ Abs.absℝ-zero)
      ∙ add-zero-right (x Add.+ x))
  ∙ cong (rationalHalf Scalar.⋆_) (double-as-two-scalar x)
  ∙ sym (scalar-assoc rationalHalf (1 ℚR.+ 1) x)
  ∙ cong (Scalar._⋆ x) ℚ!
  ∙ scalar-id x

min-idempotent : ∀ x → x ⊓ℝ x ≡ x
min-idempotent x =
  cong Neg.-_ (max-idempotent (Neg.- x))
  ∙ Neg.neg-involutive x


-- This relation already has reflexivity and antisymmetry.  Transitivity is
-- intentionally not claimed until associativity/absorption of the formula
-- operation has been established constructively.

infix 4 _≤ℝ_

_≤ℝ_ : Real.ℝ → Real.ℝ → Type
x ≤ℝ y = x ⊔ℝ y ≡ y

isProp≤ℝ : ∀ x y → isProp (x ≤ℝ y)
isProp≤ℝ x y = Real.Base.isSetCompletion _ _

≤ℝ-refl : ∀ x → x ≤ℝ x
≤ℝ-refl = max-idempotent

≤ℝ-antisym : ∀ x y → x ≤ℝ y → y ≤ℝ x → x ≡ y
≤ℝ-antisym x y x≤y y≤x =
  sym y≤x ∙ max-comm y x ∙ x≤y
