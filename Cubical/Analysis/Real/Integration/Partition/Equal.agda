module Cubical.Analysis.Real.Integration.Partition.Equal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.FinData using (Fin)
import Cubical.Data.FinData as FD
import Cubical.Data.FinData.Properties as FDP
open import Cubical.Data.Int.Fast.Base as ℤ using (pos)
import Cubical.Data.Int.Fast.Order as ℤ
import Cubical.Data.Int.Fast.Properties as ℤProp
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚAbs
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using ([k/n]≤[k'/n])

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue using
  (nonnegativeSub; 0≤→isNonnegative)
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.Partition.Properties
open import Cubical.Analysis.Real.Integration.Partition.Sampling


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)
  module ℚRing = RingTheory (CommRing→Ring ℚCommRing)

  subAddCancel : ∀ x y → (x - y) + y ≡ x
  subAddCancel x y =
    sym (addAssoc x (- y) y)
    ∙ cong (x +_) (addInvL y)
    ∙ addIdR x


-- The partition indexed by n has suc n equal subintervals.
equalFraction : (n : ℕ) → Fin (suc (suc n)) → ℚ
equalFraction n k = [ pos (FD.toℕ k) / 1+ n ]


private
  equalFraction-lower : ∀ n (i : Fin (suc n)) →
    equalFraction n (FD.weakenFin i) ≡
    [ pos (FD.toℕ i) / 1+ n ]
  equalFraction-lower n i =
    cong (λ k → [ pos k / 1+ n ]) (FDP.weakenRespToℕ i)

  equalFraction-step≤ : ∀ n (i : Fin (suc n)) →
    equalFraction n (FD.weakenFin i) ℚ.≤
    equalFraction n (FD.suc i)
  equalFraction-step≤ n i =
    subst (ℚ._≤ equalFraction n (FD.suc i))
      (sym (equalFraction-lower n i))
      ([k/n]≤[k'/n]
        (pos (FD.toℕ i)) (pos (suc (FD.toℕ i))) (1+ n)
        (ℤ.ℕ≤→pos-≤-pos
          (FD.toℕ i) (suc (FD.toℕ i)) ℕ.≤-sucℕ))

  successorDifference : ∀ m → (suc m ℤ.ℕ- m) ≡ pos 1
  successorDifference zero = refl
  successorDifference (suc m) = successorDifference m

  successorPosDifference : ∀ m →
    pos (suc m) ℤ.- pos m ≡ pos 1
  successorPosDifference m =
    sym (ℤProp.pos- (suc m) m)
    ∙ successorDifference m

  sameDenomSubSucc : ∀ m d →
    (([_/_] (pos (suc m)) d) ℚ.- ([_/_] (pos m) d)) ≡
    ([_/_] (pos (suc m) ℤ.- pos m) d)
  sameDenomSubSucc m d =
    cong₂ ℚ._-_ (ℚ.[/]≡· (pos (suc m)) d) (ℚ.[/]≡· (pos m) d)
    ∙ sym (ℚRing.·DistL-
      [ pos (suc m) / 1 ] [ pos m / 1 ] [ pos 1 / d ])
    ∙ cong (ℚ._· [ pos 1 / d ])
      (ℚAbs.ℤ-→ℚ- (pos (suc m)) (pos m))
    ∙ sym (ℚ.[/]≡· (pos (suc m) ℤ.- pos m) d)

  equalFraction-step : ∀ n (i : Fin (suc n)) →
    equalFraction n (FD.suc i) ℚ.-
    equalFraction n (FD.weakenFin i) ≡
    [ pos 1 / 1+ n ]
  equalFraction-step n i =
    cong (λ q → equalFraction n (FD.suc i) ℚ.- q)
      (equalFraction-lower n i)
    ∙ sameDenomSubSucc (FD.toℕ i) (1+ n)
    ∙ cong (λ z → [ z / 1+ n ])
      (successorPosDifference (FD.toℕ i))


equalPartition : ∀ a b → a ≤ℝ b → ℕ → Partition[ a , b ]
equalPartition a b a≤b n =
  suc n
  , (λ k → a + ((b - a) · rat (equalFraction n k)))
  , leftEndpoint
  , rightEndpoint
  , monotone
  where
  leftEndpoint :
    a + ((b - a) · rat (equalFraction n FD.zero)) ≡ a
  leftEndpoint =
    cong (a +_)
      (cong ((b - a) ·_)
        (cong rat (ℚ.[0/n]≡[0/m] n zero))
      ∙ ℝRing.0RightAnnihilates (b - a))
    ∙ addIdR a

  rightEndpoint :
    a + ((b - a) · rat (equalFraction n (FD.fromℕ (suc n)))) ≡ b
  rightEndpoint =
    cong (a +_)
      (cong ((b - a) ·_)
        (cong rat
          (cong (λ k → [ pos k / 1+ n ]) (FD.toFromId (suc n))
          ∙ ℚ.[n/n]≡[m/m] n zero))
      ∙ mulIdR (b - a))
    ∙ addComm a (b - a)
    ∙ subAddCancel b a

  monotone : (i : Fin (suc n)) →
    a + ((b - a) · rat (equalFraction n (FD.weakenFin i))) ≤ℝ
    a + ((b - a) · rat (equalFraction n (FD.suc i)))
  monotone i =
    addPres≤L
      ((b - a) · rat (equalFraction n (FD.weakenFin i)))
      ((b - a) · rat (equalFraction n (FD.suc i))) a
      (mulPres≤L
        (rat (equalFraction n (FD.weakenFin i)))
        (rat (equalFraction n (FD.suc i))) (b - a)
        (0≤→isNonnegative (b - a) (nonnegativeSub a b a≤b))
        (invEq
          (rat≤rat≃
            (equalFraction n (FD.weakenFin i))
            (equalFraction n (FD.suc i)))
          (equalFraction-step≤ n i)))


equalPartition-width : ∀ a b (a≤b : a ≤ℝ b) n
  (i : Fin (suc n)) →
  width (equalPartition a b a≤b n) i ≡
  (b - a) · rat [ pos 1 / 1+ n ]
equalPartition-width a b a≤b n i =
  sym (ℝRing.translatedDifference a
    ((b - a) · rat (equalFraction n (FD.suc i)))
    ((b - a) · rat (equalFraction n (FD.weakenFin i))))
  ∙ sym (ℝRing.·DistR-
    (b - a)
    (rat (equalFraction n (FD.suc i)))
    (rat (equalFraction n (FD.weakenFin i))))
  ∙ cong ((b - a) ·_)
      (sub-rat
        (equalFraction n (FD.suc i))
        (equalFraction n (FD.weakenFin i)))
  ∙ cong (λ q → (b - a) · rat q)
      (equalFraction-step n i)


equalLeftTaggedPartition : ∀ a b → a ≤ℝ b → ℕ →
  TaggedPartition[ a , b ]
equalLeftTaggedPartition a b a≤b n =
  leftTaggedPartition (equalPartition a b a≤b n)


equalRightTaggedPartition : ∀ a b → a ≤ℝ b → ℕ →
  TaggedPartition[ a , b ]
equalRightTaggedPartition a b a≤b n =
  rightTaggedPartition (equalPartition a b a≤b n)
