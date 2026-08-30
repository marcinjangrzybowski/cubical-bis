module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.FiniteSum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (x≤abs ; add-monotone ; abs-triangle)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
  using (partialSumShiftDifference)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Order
  using (partialSumMono)


-- Finite triangle inequality for the partial-sum convention used here.

partialSumAbsBound : ∀ terms n →
  Abs.absℝ (partialSum terms n) ≤ℝ
  partialSum (Abs.absℝ ∘ terms) n
partialSumAbsBound terms zero =
  subst (λ z → z ≤ℝ zeroℝ)
    (sym Abs.absℝ-zero)
    (≤ℝ-refl zeroℝ)
partialSumAbsBound terms (suc n) =
  ≤ℝ-trans
    (Abs.absℝ (partialSum terms n Add.+ terms n))
    (Abs.absℝ (partialSum terms n) Add.+ Abs.absℝ (terms n))
    (partialSum (Abs.absℝ ∘ terms) n Add.+ Abs.absℝ (terms n))
    (abs-triangle (partialSum terms n) (terms n))
    (add-monotone
      (Abs.absℝ (partialSum terms n))
      (partialSum (Abs.absℝ ∘ terms) n)
      (Abs.absℝ (terms n)) (Abs.absℝ (terms n))
      (partialSumAbsBound terms n)
      (≤ℝ-refl (Abs.absℝ (terms n))))


partialSumShiftAbsDifferenceBound :
  (terms : RealSequence) → (start count : ℕ) →
  Abs.absℝ
    (partialSum terms (count ℕ.+ start)
      Group.- partialSum terms start) ≤ℝ
  partialSum (Abs.absℝ ∘ terms) (count ℕ.+ start)
    Group.- partialSum (Abs.absℝ ∘ terms) start
partialSumShiftAbsDifferenceBound terms start count =
  subst2 _≤ℝ_
    (cong Abs.absℝ
      (sym (partialSumShiftDifference terms start count)))
    (sym (partialSumShiftDifference
      (Abs.absℝ ∘ terms) start count))
    (partialSumAbsBound
      (λ k → terms (k ℕ.+ start)) count)


orderedPartialSumDistanceBound :
  (terms : RealSequence) → (m n : ℕ) →
  m ℕ.≤ n →
  Abs.absℝ
    (partialSum terms n Group.- partialSum terms m) ≤ℝ
  Abs.absℝ
    (partialSum (Abs.absℝ ∘ terms) n
      Group.- partialSum (Abs.absℝ ∘ terms) m)
orderedPartialSumDistanceBound terms m n m≤n =
  ≤ℝ-trans
    (Abs.absℝ (partialSum terms n Group.- partialSum terms m))
    (partialSum (Abs.absℝ ∘ terms) n
      Group.- partialSum (Abs.absℝ ∘ terms) m)
    (Abs.absℝ
      (partialSum (Abs.absℝ ∘ terms) n
        Group.- partialSum (Abs.absℝ ∘ terms) m))
    tailBound
    (x≤abs
      (partialSum (Abs.absℝ ∘ terms) n
        Group.- partialSum (Abs.absℝ ∘ terms) m))
  where
  count : ℕ
  count = n ℕ.∸ m

  count+m≡n : count ℕ.+ m ≡ n
  count+m≡n = ℕ.[n-m]+m m n m≤n

  tailBound :
    Abs.absℝ
      (partialSum terms n Group.- partialSum terms m) ≤ℝ
    partialSum (Abs.absℝ ∘ terms) n
      Group.- partialSum (Abs.absℝ ∘ terms) m
  tailBound =
    subst
      (λ k →
        Abs.absℝ
          (partialSum terms k Group.- partialSum terms m) ≤ℝ
        partialSum (Abs.absℝ ∘ terms) k
          Group.- partialSum (Abs.absℝ ∘ terms) m)
      count+m≡n
      (partialSumShiftAbsDifferenceBound terms m count)


private
  absSubComm : ∀ x y →
    Abs.absℝ (x Group.- y) ≡ Abs.absℝ (y Group.- x)
  absSubComm x y =
    sym (Abs.absℝ-neg (x Group.- y))
    ∙ cong Abs.absℝ (neg-sub x y)

  swapPartialSumDistanceBound :
    (terms : RealSequence) → (m n : ℕ) →
    Abs.absℝ
      (partialSum terms m Group.- partialSum terms n) ≤ℝ
    Abs.absℝ
      (partialSum (Abs.absℝ ∘ terms) m
        Group.- partialSum (Abs.absℝ ∘ terms) n) →
    Abs.absℝ
      (partialSum terms n Group.- partialSum terms m) ≤ℝ
    Abs.absℝ
      (partialSum (Abs.absℝ ∘ terms) n
        Group.- partialSum (Abs.absℝ ∘ terms) m)
  swapPartialSumDistanceBound terms m n =
    subst2 _≤ℝ_
      (absSubComm (partialSum terms m) (partialSum terms n))
      (absSubComm
        (partialSum (Abs.absℝ ∘ terms) m)
        (partialSum (Abs.absℝ ∘ terms) n))


partialSumDistanceBound :
  (terms : RealSequence) → (m n : ℕ) →
  Abs.absℝ
    (partialSum terms m Group.- partialSum terms n) ≤ℝ
  Abs.absℝ
    (partialSum (Abs.absℝ ∘ terms) m
      Group.- partialSum (Abs.absℝ ∘ terms) n)
partialSumDistanceBound terms =
  ℕ.elimBy≤
    (swapPartialSumDistanceBound terms)
    λ m n m≤n →
      swapPartialSumDistanceBound terms n m
        (orderedPartialSumDistanceBound terms m n m≤n)


partialSumShiftDistanceBoundBy :
  (terms bound : RealSequence) →
  (∀ n → Abs.absℝ (terms n) ≤ℝ bound n) →
  (start count : ℕ) →
  Abs.absℝ
    (partialSum terms (count ℕ.+ start)
      Group.- partialSum terms start) ≤ℝ
  partialSum bound (count ℕ.+ start)
    Group.- partialSum bound start
partialSumShiftDistanceBoundBy
  terms bound dominates start count =
  subst2 _≤ℝ_
    (cong Abs.absℝ
      (sym (partialSumShiftDifference terms start count)))
    (sym (partialSumShiftDifference bound start count))
    shiftedBound
  where
  shiftedTerms : RealSequence
  shiftedTerms k = terms (k ℕ.+ start)

  shiftedBoundTerms : RealSequence
  shiftedBoundTerms k = bound (k ℕ.+ start)

  shiftedBound :
    Abs.absℝ (partialSum shiftedTerms count) ≤ℝ
    partialSum shiftedBoundTerms count
  shiftedBound =
    ≤ℝ-trans
      (Abs.absℝ (partialSum shiftedTerms count))
      (partialSum (Abs.absℝ ∘ shiftedTerms) count)
      (partialSum shiftedBoundTerms count)
      (partialSumAbsBound shiftedTerms count)
      (partialSumMono
        (Abs.absℝ ∘ shiftedTerms) shiftedBoundTerms
        (λ k → dominates (k ℕ.+ start)) count)


orderedPartialSumDistanceBoundBy :
  (terms bound : RealSequence) →
  (∀ n → Abs.absℝ (terms n) ≤ℝ bound n) →
  (m n : ℕ) → m ℕ.≤ n →
  Abs.absℝ
    (partialSum terms n Group.- partialSum terms m) ≤ℝ
  Abs.absℝ
    (partialSum bound n Group.- partialSum bound m)
orderedPartialSumDistanceBoundBy
  terms bound dominates m n m≤n =
  ≤ℝ-trans
    (Abs.absℝ (partialSum terms n Group.- partialSum terms m))
    (partialSum bound n Group.- partialSum bound m)
    (Abs.absℝ (partialSum bound n Group.- partialSum bound m))
    tailBound
    (x≤abs (partialSum bound n Group.- partialSum bound m))
  where
  count : ℕ
  count = n ℕ.∸ m

  count+m≡n : count ℕ.+ m ≡ n
  count+m≡n = ℕ.[n-m]+m m n m≤n

  tailBound :
    Abs.absℝ
      (partialSum terms n Group.- partialSum terms m) ≤ℝ
    partialSum bound n Group.- partialSum bound m
  tailBound =
    subst
      (λ k →
        Abs.absℝ
          (partialSum terms k Group.- partialSum terms m) ≤ℝ
        partialSum bound k Group.- partialSum bound m)
      count+m≡n
      (partialSumShiftDistanceBoundBy
        terms bound dominates m count)


private
  swapPartialSumDistanceBoundBy :
    (terms bound : RealSequence) → (m n : ℕ) →
    Abs.absℝ
      (partialSum terms m Group.- partialSum terms n) ≤ℝ
    Abs.absℝ
      (partialSum bound m Group.- partialSum bound n) →
    Abs.absℝ
      (partialSum terms n Group.- partialSum terms m) ≤ℝ
    Abs.absℝ
      (partialSum bound n Group.- partialSum bound m)
  swapPartialSumDistanceBoundBy terms bound m n =
    subst2 _≤ℝ_
      (absSubComm (partialSum terms m) (partialSum terms n))
      (absSubComm (partialSum bound m) (partialSum bound n))


partialSumDistanceBoundBy :
  (terms bound : RealSequence) →
  (∀ n → Abs.absℝ (terms n) ≤ℝ bound n) →
  (m n : ℕ) →
  Abs.absℝ
    (partialSum terms m Group.- partialSum terms n) ≤ℝ
  Abs.absℝ
    (partialSum bound m Group.- partialSum bound n)
partialSumDistanceBoundBy terms bound dominates =
  ℕ.elimBy≤
    (swapPartialSumDistanceBoundBy terms bound)
    λ m n m≤n →
      swapPartialSumDistanceBoundBy terms bound n m
        (orderedPartialSumDistanceBoundBy
          terms bound dominates m n m≤n)
