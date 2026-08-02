module Cubical.HITs.CauchyRealsP.Analysis.Series.FiniteSum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base

partialSumShiftDifference :
  (terms : RealSequence) → (start count : ℕ) →
  partialSum terms (count ℕ.+ start)
    - partialSum terms start ≡
  partialSum (λ k → terms (k ℕ.+ start)) count
partialSumShiftDifference terms start zero =
  subSelf (partialSum terms start)
partialSumShiftDifference terms start (suc count) =
  cong (_+ (- partialSum terms start))
    (addComm
      (partialSum terms (count ℕ.+ start))
      (terms (count ℕ.+ start)))
  ∙ sym
      (addAssoc
        (terms (count ℕ.+ start))
        (partialSum terms (count ℕ.+ start))
        (- partialSum terms start))
  ∙ cong (terms (count ℕ.+ start) +_)
      (partialSumShiftDifference terms start count)
  ∙ addComm
      (terms (count ℕ.+ start))
      (partialSum
        (λ k → terms (k ℕ.+ start)) count)

partialSumShiftAbsDifferenceBound :
  (terms : RealSequence) → (start count : ℕ) →
  absℝ
    (partialSum terms (count ℕ.+ start)
      - partialSum terms start)
    ≤ℝ
  partialSum (absℝ ∘ terms) (count ℕ.+ start)
    - partialSum (absℝ ∘ terms) start
partialSumShiftAbsDifferenceBound terms start count =
  subst2 _≤ℝ_
    (cong absℝ
      (sym
        (partialSumShiftDifference
          terms start count)))
    (sym
      (partialSumShiftDifference
        (absℝ ∘ terms) start count))
    (partialSumAbsBound
      (λ k → terms (k ℕ.+ start))
      count)

orderedPartialSumDistanceBound :
  (terms : RealSequence) → (m n : ℕ) →
  m ℕ.≤ n →
  absℝ
    (partialSum terms n - partialSum terms m)
    ≤ℝ
  absℝ
    (partialSum (absℝ ∘ terms) n
      - partialSum (absℝ ∘ terms) m)
orderedPartialSumDistanceBound terms m n m≤n =
  ≤ℝ-trans
    (absℝ
      (partialSum terms n - partialSum terms m))
    (partialSum (absℝ ∘ terms) n
      - partialSum (absℝ ∘ terms) m)
    (absℝ
      (partialSum (absℝ ∘ terms) n
        - partialSum (absℝ ∘ terms) m))
    tailBound
    (leAbs
      (partialSum (absℝ ∘ terms) n
        - partialSum (absℝ ∘ terms) m))
  where
  count : ℕ
  count =
    n ℕ.∸ m

  count+m≡n : count ℕ.+ m ≡ n
  count+m≡n =
    ℕ.[n-m]+m m n m≤n

  tailBound :
    absℝ
      (partialSum terms n - partialSum terms m)
      ≤ℝ
    partialSum (absℝ ∘ terms) n
      - partialSum (absℝ ∘ terms) m
  tailBound =
    subst
      (λ k →
        absℝ
          (partialSum terms k - partialSum terms m)
          ≤ℝ
        partialSum (absℝ ∘ terms) k
          - partialSum (absℝ ∘ terms) m)
      count+m≡n
      (partialSumShiftAbsDifferenceBound
        terms m count)

private
  swapPartialSumDistanceBound :
    (terms : RealSequence) → (m n : ℕ) →
    absℝ
      (partialSum terms m - partialSum terms n)
      ≤ℝ
    absℝ
      (partialSum (absℝ ∘ terms) m
        - partialSum (absℝ ∘ terms) n) →
    absℝ
      (partialSum terms n - partialSum terms m)
      ≤ℝ
    absℝ
      (partialSum (absℝ ∘ terms) n
        - partialSum (absℝ ∘ terms) m)
  swapPartialSumDistanceBound terms m n =
    subst2 _≤ℝ_
      (absSubComm
        (partialSum terms m)
        (partialSum terms n))
      (absSubComm
        (partialSum (absℝ ∘ terms) m)
        (partialSum (absℝ ∘ terms) n))

partialSumDistanceBound :
  (terms : RealSequence) → (m n : ℕ) →
  absℝ
    (partialSum terms m - partialSum terms n)
    ≤ℝ
  absℝ
    (partialSum (absℝ ∘ terms) m
      - partialSum (absℝ ∘ terms) n)
partialSumDistanceBound terms =
  ℕ.elimBy≤
    (swapPartialSumDistanceBound terms)
    λ m n m≤n →
      swapPartialSumDistanceBound terms n m
        (orderedPartialSumDistanceBound
          terms m n m≤n)

partialSumShiftDistanceBoundBy :
  (terms bound : RealSequence) →
  (∀ n → absℝ (terms n) ≤ℝ bound n) →
  (start count : ℕ) →
  absℝ
    (partialSum terms (count ℕ.+ start)
      - partialSum terms start)
    ≤ℝ
  partialSum bound (count ℕ.+ start)
    - partialSum bound start
partialSumShiftDistanceBoundBy
  terms bound dominates start count =
    subst2 _≤ℝ_
      (cong absℝ
        (sym
          (partialSumShiftDifference
            terms start count)))
      (sym
        (partialSumShiftDifference
          bound start count))
      shiftedBound
  where
  shiftedTerms : RealSequence
  shiftedTerms k =
    terms (k ℕ.+ start)

  shiftedBoundTerms : RealSequence
  shiftedBoundTerms k =
    bound (k ℕ.+ start)

  shiftedBound :
    absℝ (partialSum shiftedTerms count) ≤ℝ
    partialSum shiftedBoundTerms count
  shiftedBound =
    ≤ℝ-trans
      (absℝ (partialSum shiftedTerms count))
      (partialSum (absℝ ∘ shiftedTerms) count)
      (partialSum shiftedBoundTerms count)
      (partialSumAbsBound shiftedTerms count)
      (partialSumMono
        (absℝ ∘ shiftedTerms)
        shiftedBoundTerms
        (λ k → dominates (k ℕ.+ start))
        count)

orderedPartialSumDistanceBoundBy :
  (terms bound : RealSequence) →
  (∀ n → absℝ (terms n) ≤ℝ bound n) →
  (m n : ℕ) →
  m ℕ.≤ n →
  absℝ
    (partialSum terms n - partialSum terms m)
    ≤ℝ
  absℝ
    (partialSum bound n - partialSum bound m)
orderedPartialSumDistanceBoundBy
  terms bound dominates m n m≤n =
    ≤ℝ-trans
      (absℝ
        (partialSum terms n - partialSum terms m))
      (partialSum bound n - partialSum bound m)
      (absℝ
        (partialSum bound n - partialSum bound m))
      tailBound
      (leAbs
        (partialSum bound n - partialSum bound m))
  where
  count : ℕ
  count =
    n ℕ.∸ m

  count+m≡n : count ℕ.+ m ≡ n
  count+m≡n =
    ℕ.[n-m]+m m n m≤n

  tailBound :
    absℝ
      (partialSum terms n - partialSum terms m)
      ≤ℝ
    partialSum bound n - partialSum bound m
  tailBound =
    subst
      (λ k →
        absℝ
          (partialSum terms k - partialSum terms m)
          ≤ℝ
        partialSum bound k - partialSum bound m)
      count+m≡n
      (partialSumShiftDistanceBoundBy
        terms bound dominates m count)

private
  swapPartialSumDistanceBoundBy :
    (terms bound : RealSequence) →
    (m n : ℕ) →
    absℝ
      (partialSum terms m - partialSum terms n)
      ≤ℝ
    absℝ
      (partialSum bound m - partialSum bound n) →
    absℝ
      (partialSum terms n - partialSum terms m)
      ≤ℝ
    absℝ
      (partialSum bound n - partialSum bound m)
  swapPartialSumDistanceBoundBy
    terms bound m n =
      subst2 _≤ℝ_
        (absSubComm
          (partialSum terms m)
          (partialSum terms n))
        (absSubComm
          (partialSum bound m)
          (partialSum bound n))

partialSumDistanceBoundBy :
  (terms bound : RealSequence) →
  (∀ n → absℝ (terms n) ≤ℝ bound n) →
  (m n : ℕ) →
  absℝ
    (partialSum terms m - partialSum terms n)
    ≤ℝ
  absℝ
    (partialSum bound m - partialSum bound n)
partialSumDistanceBoundBy terms bound dominates =
  ℕ.elimBy≤
    (swapPartialSumDistanceBoundBy terms bound)
    λ m n m≤n →
      swapPartialSumDistanceBoundBy
        terms bound n m
        (orderedPartialSumDistanceBoundBy
          terms bound dominates m n m≤n)
