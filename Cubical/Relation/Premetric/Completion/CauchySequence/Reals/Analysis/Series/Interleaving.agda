module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Interleaving where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc ; doubleℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base


-- Insert one zero after every term.  This is the series-level operation
-- needed by even power-series substitutions: it changes the clock of the
-- partial sums, but neither their value nor their limit.

zeroInterleave : RealSequence → RealSequence
zeroInterleave terms zero = terms zero
zeroInterleave terms (suc zero) = zeroℝ
zeroInterleave terms (suc (suc n)) =
  zeroInterleave (terms ∘ suc) n


zeroInterleave-even : ∀ terms n →
  zeroInterleave terms (doubleℕ n) ≡ terms n
zeroInterleave-even terms zero = refl
zeroInterleave-even terms (suc n) =
  zeroInterleave-even (terms ∘ suc) n


zeroInterleave-odd : ∀ terms n →
  zeroInterleave terms (suc (doubleℕ n)) ≡ zeroℝ
zeroInterleave-odd terms zero = refl
zeroInterleave-odd terms (suc n) =
  zeroInterleave-odd (terms ∘ suc) n


-- At an even clock the interleaved partial sum is exactly the original
-- partial sum.  At an odd clock it has already consumed the next nonzero
-- term.  These exact identities make the limit transfer independent of any
-- metric estimate.

zeroInterleavePartialSum-even : ∀ terms n →
  partialSum (zeroInterleave terms) (doubleℕ n)
    ≡ partialSum terms n
zeroInterleavePartialSum-even terms zero = refl
zeroInterleavePartialSum-even terms (suc n) =
    cong
      (Add._+ zeroInterleave terms (suc (doubleℕ n)))
      (cong₂ Add._+_
        (zeroInterleavePartialSum-even terms n)
        (zeroInterleave-even terms n))
  ∙ cong
      ((partialSum terms n Add.+ terms n) Add.+_)
      (zeroInterleave-odd terms n)
  ∙ add-zero-right (partialSum terms n Add.+ terms n)


zeroInterleavePartialSum-odd : ∀ terms n →
  partialSum (zeroInterleave terms) (suc (doubleℕ n))
    ≡ partialSum terms (suc n)
zeroInterleavePartialSum-odd terms n =
  cong₂ Add._+_
    (zeroInterleavePartialSum-even terms n)
    (zeroInterleave-even terms n)


private
  data IndexParity : ℕ → Type₀ where
    even : ∀ n → IndexParity (doubleℕ n)
    odd  : ∀ n → IndexParity (suc (doubleℕ n))

  indexParity : ∀ n → IndexParity n
  indexParity zero = even zero
  indexParity (suc zero) = odd zero
  indexParity (suc (suc n)) with indexParity n
  ... | even k = even (suc k)
  ... | odd k = odd (suc k)

  double≤double→≤ : ∀ {m n} →
    doubleℕ m ℕ.≤ doubleℕ n → m ℕ.≤ n
  double≤double→≤ {zero} {n} _ = ℕ.zero-≤
  double≤double→≤ {suc m} {zero} impossible =
    ⊥.rec (ℕ.¬-<-zero impossible)
  double≤double→≤ {suc m} {suc n} bound =
    ℕ.suc-≤-suc
      (double≤double→≤
        (ℕ.pred-≤-pred (ℕ.pred-≤-pred bound)))

  double≤odd→≤ : ∀ {m n} →
    doubleℕ m ℕ.≤ suc (doubleℕ n) → m ℕ.≤ n
  double≤odd→≤ {zero} {n} _ = ℕ.zero-≤
  double≤odd→≤ {suc m} {zero} impossible =
    ⊥.rec (ℕ.¬-<-zero (ℕ.pred-≤-pred impossible))
  double≤odd→≤ {suc m} {suc n} bound =
    ℕ.suc-≤-suc
      (double≤odd→≤
        (ℕ.pred-≤-pred (ℕ.pred-≤-pred bound)))


-- This preservation theorem is stronger than mere summability: it retains
-- the specified sum.  Only the already-truncated tail at each radius is
-- opened, and the output tail is immediately truncated again.

zeroInterleaveHasSum : ∀ terms value →
  HasSum terms value →
  HasSum (zeroInterleave terms) value
zeroInterleaveHasSum terms value terms-sum ε =
  PT.map stretch-tail (terms-sum ε)
  where
  stretch-tail :
    Σ[ N ∈ ℕ ]
      (∀ n → N ℕ.≤ n →
        partialSum terms n Real.Base.≈ᶜ[ ε ] value) →
    Σ[ N ∈ ℕ ]
      (∀ n → N ℕ.≤ n →
        partialSum (zeroInterleave terms) n
          Real.Base.≈ᶜ[ ε ] value)
  stretch-tail (N , close) =
    doubleℕ N , close-after-double
    where
    close-after-double : ∀ n →
      doubleℕ N ℕ.≤ n →
      partialSum (zeroInterleave terms) n
        Real.Base.≈ᶜ[ ε ] value
    close-after-double n late with indexParity n
    ... | even k =
      subst
        (λ point → point Real.Base.≈ᶜ[ ε ] value)
        (sym (zeroInterleavePartialSum-even terms k))
        (close k (double≤double→≤ late))
    ... | odd k =
      subst
        (λ point → point Real.Base.≈ᶜ[ ε ] value)
        (sym (zeroInterleavePartialSum-odd terms k))
        (close (suc k)
          (ℕ.≤-trans (double≤odd→≤ late) ℕ.≤-sucℕ))


zeroInterleaveSummable : ∀ terms →
  Summable terms → Summable (zeroInterleave terms)
zeroInterleaveSummable terms (value , terms-sum) =
  value , zeroInterleaveHasSum terms value terms-sum
