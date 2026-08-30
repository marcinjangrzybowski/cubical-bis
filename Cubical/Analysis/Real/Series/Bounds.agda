module Cubical.Analysis.Real.Series.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; _∸_)
open import Cubical.Data.Nat.Order as ℕ

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Tails


partialSumMono : ∀ a b →
  (∀ n → a n ≤ℝ b n) →
  ∀ n → partialSum a n ≤ℝ partialSum b n
partialSumMono a b pointwise zero =
  ≤ℝ-refl 0ℝ
partialSumMono a b pointwise (suc n) =
  addPres≤
    (partialSum a n) (partialSum b n)
    (a n) (b n)
    (partialSumMono a b pointwise n)
    (pointwise n)


partialSumIndexMono : ∀ terms →
  (∀ n → 0ℝ ≤ℝ terms n) →
  ∀ m n → m ℕ.≤ n →
  partialSum terms m ≤ℝ partialSum terms n
partialSumIndexMono terms nonnegative m n m≤n =
  subst
    (λ k → partialSum terms m ≤ℝ partialSum terms k)
    (ℕ.≤-∸-+-cancel m≤n)
    (go (n ∸ m))
  where
  go : ∀ count →
    partialSum terms m ≤ℝ
    partialSum terms (count ℕ.+ m)
  go zero = ≤ℝ-refl (partialSum terms m)
  go (suc count) =
    ≤ℝ-trans
      (partialSum terms m)
      (partialSum terms (count ℕ.+ m))
      (partialSum terms (count ℕ.+ m)
        + terms (count ℕ.+ m))
      (go count)
      (subst
        (_≤ℝ partialSum terms (count ℕ.+ m)
          + terms (count ℕ.+ m))
        (addIdR (partialSum terms (count ℕ.+ m)))
        (addPres≤
          (partialSum terms (count ℕ.+ m))
          (partialSum terms (count ℕ.+ m))
          0ℝ (terms (count ℕ.+ m))
          (≤ℝ-refl (partialSum terms (count ℕ.+ m)))
          (nonnegative (count ℕ.+ m))))


partialSumNonnegative : ∀ terms →
  (∀ n → 0ℝ ≤ℝ terms n) →
  ∀ n → 0ℝ ≤ℝ partialSum terms n
partialSumNonnegative terms nonnegative n =
  subst
    (_≤ℝ partialSum terms n)
    (sym (partialSum-zero terms))
    (partialSumIndexMono
      terms nonnegative zero n ℕ.zero-≤)


partialSumAbsBound : ∀ terms n →
  absℝ (partialSum terms n) ≤ℝ
  partialSum (absℝ ∘ terms) n
partialSumAbsBound terms zero =
  subst (_≤ℝ 0ℝ)
    (sym absZero) (≤ℝ-refl 0ℝ)
partialSumAbsBound terms (suc n) =
  ≤ℝ-trans
    (absℝ (partialSum terms n + terms n))
    (absℝ (partialSum terms n) + absℝ (terms n))
    (partialSum (absℝ ∘ terms) n + absℝ (terms n))
    (absTriangle (partialSum terms n) (terms n))
    (addPres≤
      (absℝ (partialSum terms n))
      (partialSum (absℝ ∘ terms) n)
      (absℝ (terms n)) (absℝ (terms n))
      (partialSumAbsBound terms n)
      (≤ℝ-refl (absℝ (terms n))))


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
      (sym (partialSumShiftDifference terms start count)))
    (sym (partialSumShiftDifference
      (absℝ ∘ terms) start count))
    (partialSumAbsBound (dropSeries start terms) count)


orderedPartialSumDistanceBound :
  (terms : RealSequence) → (m n : ℕ) →
  m ℕ.≤ n →
  absℝ (partialSum terms n - partialSum terms m) ≤ℝ
  absℝ
    (partialSum (absℝ ∘ terms) n
      - partialSum (absℝ ∘ terms) m)
orderedPartialSumDistanceBound terms m n m≤n =
  ≤ℝ-trans
    (absℝ (partialSum terms n - partialSum terms m))
    (partialSum (absℝ ∘ terms) n
      - partialSum (absℝ ∘ terms) m)
    (absℝ
      (partialSum (absℝ ∘ terms) n
        - partialSum (absℝ ∘ terms) m))
    tail-bound
    (leAbs
      (partialSum (absℝ ∘ terms) n
        - partialSum (absℝ ∘ terms) m))
  where
  count : ℕ
  count = n ∸ m

  count+m≡n : count ℕ.+ m ≡ n
  count+m≡n = ℕ.≤-∸-+-cancel m≤n

  tail-bound :
    absℝ (partialSum terms n - partialSum terms m) ≤ℝ
    partialSum (absℝ ∘ terms) n
      - partialSum (absℝ ∘ terms) m
  tail-bound =
    subst
      (λ k →
        absℝ (partialSum terms k - partialSum terms m) ≤ℝ
        partialSum (absℝ ∘ terms) k
          - partialSum (absℝ ∘ terms) m)
      count+m≡n
      (partialSumShiftAbsDifferenceBound terms m count)


private
  swapPartialSumDistanceBound :
    (terms : RealSequence) → (m n : ℕ) →
    absℝ (partialSum terms m - partialSum terms n) ≤ℝ
    absℝ
      (partialSum (absℝ ∘ terms) m
        - partialSum (absℝ ∘ terms) n) →
    absℝ (partialSum terms n - partialSum terms m) ≤ℝ
    absℝ
      (partialSum (absℝ ∘ terms) n
        - partialSum (absℝ ∘ terms) m)
  swapPartialSumDistanceBound terms m n =
    subst2 _≤ℝ_
      (absSubComm (partialSum terms m) (partialSum terms n))
      (absSubComm
        (partialSum (absℝ ∘ terms) m)
        (partialSum (absℝ ∘ terms) n))


partialSumDistanceBound :
  (terms : RealSequence) → (m n : ℕ) →
  absℝ (partialSum terms m - partialSum terms n) ≤ℝ
  absℝ
    (partialSum (absℝ ∘ terms) m
      - partialSum (absℝ ∘ terms) n)
partialSumDistanceBound terms =
  ℕ.elimBy≤
    (swapPartialSumDistanceBound terms)
    λ m n m≤n →
      swapPartialSumDistanceBound terms n m
        (orderedPartialSumDistanceBound terms m n m≤n)


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
      (sym (partialSumShiftDifference terms start count)))
    (sym (partialSumShiftDifference bound start count))
    shifted-bound
  where
  shifted-terms : RealSequence
  shifted-terms = dropSeries start terms

  shifted-bound-terms : RealSequence
  shifted-bound-terms = dropSeries start bound

  shifted-bound :
    absℝ (partialSum shifted-terms count) ≤ℝ
    partialSum shifted-bound-terms count
  shifted-bound =
    ≤ℝ-trans
      (absℝ (partialSum shifted-terms count))
      (partialSum (absℝ ∘ shifted-terms) count)
      (partialSum shifted-bound-terms count)
      (partialSumAbsBound shifted-terms count)
      (partialSumMono
        (absℝ ∘ shifted-terms) shifted-bound-terms
        (λ k → dominates (k ℕ.+ start)) count)


orderedPartialSumDistanceBoundBy :
  (terms bound : RealSequence) →
  (∀ n → absℝ (terms n) ≤ℝ bound n) →
  (m n : ℕ) → m ℕ.≤ n →
  absℝ (partialSum terms n - partialSum terms m) ≤ℝ
  absℝ (partialSum bound n - partialSum bound m)
orderedPartialSumDistanceBoundBy
    terms bound dominates m n m≤n =
  ≤ℝ-trans
    (absℝ (partialSum terms n - partialSum terms m))
    (partialSum bound n - partialSum bound m)
    (absℝ (partialSum bound n - partialSum bound m))
    tail-bound
    (leAbs (partialSum bound n - partialSum bound m))
  where
  count : ℕ
  count = n ∸ m

  count+m≡n : count ℕ.+ m ≡ n
  count+m≡n = ℕ.≤-∸-+-cancel m≤n

  tail-bound :
    absℝ (partialSum terms n - partialSum terms m) ≤ℝ
    partialSum bound n - partialSum bound m
  tail-bound =
    subst
      (λ k →
        absℝ (partialSum terms k - partialSum terms m) ≤ℝ
        partialSum bound k - partialSum bound m)
      count+m≡n
      (partialSumShiftDistanceBoundBy
        terms bound dominates m count)


private
  swapPartialSumDistanceBoundBy :
    (terms bound : RealSequence) → (m n : ℕ) →
    absℝ (partialSum terms m - partialSum terms n) ≤ℝ
    absℝ (partialSum bound m - partialSum bound n) →
    absℝ (partialSum terms n - partialSum terms m) ≤ℝ
    absℝ (partialSum bound n - partialSum bound m)
  swapPartialSumDistanceBoundBy terms bound m n =
    subst2 _≤ℝ_
      (absSubComm (partialSum terms m) (partialSum terms n))
      (absSubComm (partialSum bound m) (partialSum bound n))


partialSumDistanceBoundBy :
  (terms bound : RealSequence) →
  (∀ n → absℝ (terms n) ≤ℝ bound n) →
  (m n : ℕ) →
  absℝ (partialSum terms m - partialSum terms n) ≤ℝ
  absℝ (partialSum bound m - partialSum bound n)
partialSumDistanceBoundBy terms bound dominates =
  ℕ.elimBy≤
    (swapPartialSumDistanceBoundBy terms bound)
    λ m n m≤n →
      swapPartialSumDistanceBoundBy terms bound n m
        (orderedPartialSumDistanceBoundBy
          terms bound dominates m n m≤n)
