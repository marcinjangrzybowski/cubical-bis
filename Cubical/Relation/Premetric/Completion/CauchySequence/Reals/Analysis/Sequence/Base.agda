module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real

module Theory = PremetricTheory Real.ℝPremetricSpace


-- Two notions of Cauchy sequence -----------------------------------------
--
-- `ChosenIsCauchySequence` is the traditional library notion.  It contains
-- one function choosing a tail index at every positive rational radius.
-- `IsCauchySequence` is native to this completion: the tail at each radius
-- merely exists, independently of the tails at all other radii.

CauchyTail : (ℕ → Real.ℝ) → ℚ₊ → Type₀
CauchyTail = Real.Base.CauchyTail

IsCauchySequence : (ℕ → Real.ℝ) → Type₀
IsCauchySequence = Real.Base.IsCauchySequence

isPropIsCauchySequence : ∀ x → isProp (IsCauchySequence x)
isPropIsCauchySequence = Real.Base.isPropIsCauchySequence

ChosenIsCauchySequence : (ℕ → Real.ℝ) → Type₀
ChosenIsCauchySequence = Theory.isCauchySeq

MerelyChosenIsCauchySequence : (ℕ → Real.ℝ) → Type₀
MerelyChosenIsCauchySequence x = ∥ ChosenIsCauchySequence x ∥₁


chosen→radiuswise : ∀ {x} →
  ChosenIsCauchySequence x → IsCauchySequence x
chosen→radiuswise (modulus , close) ε =
  ∣ modulus ε , close ε ∣₁


merelyChosen→radiuswise : ∀ {x} →
  MerelyChosenIsCauchySequence x → IsCauchySequence x
merelyChosen→radiuswise {x} =
  PT.rec (isPropIsCauchySequence x) chosen→radiuswise


-- We deliberately provide no converse here.  Such a converse would commute
-- a product over all radii with propositional truncation, exactly the
-- tail-choice principle isolated by `Completion.Comparison`.


-- Sequential limits ------------------------------------------------------
--
-- Convergence already uses the good truncation placement: for each radius
-- there merely exists a tail close to the proposed limit.  The carrier of a
-- limit is not truncated, because separatedness makes the entire type of
-- limits a proposition.

isLimitSequence : (ℕ → Real.ℝ) → Real.ℝ → Type₀
isLimitSequence = Theory.isLimitSeq

isPropIsLimitSequence : ∀ x l →
  isProp (isLimitSequence x l)
isPropIsLimitSequence = Theory.isPropIsLimitSeq

SequenceLimit : (ℕ → Real.ℝ) → Type₀
SequenceLimit = Theory.limitSeq

isPropSequenceLimit : ∀ x → isProp (SequenceLimit x)
isPropSequenceLimit = Theory.isPropLimitSeq


-- The native constructor accepts the radiuswise witness directly.  In
-- contrast with the regular-real construction, no simultaneous modulus is
-- selected before taking the limit.

cauchySequenceLimit : ∀ x →
  IsCauchySequence x → SequenceLimit x
cauchySequenceLimit = Real.hasCauchySequenceLimitsℝ


limitOfCauchySequence : ∀ x →
  IsCauchySequence x → Real.ℝ
limitOfCauchySequence x gx = Real.Base.lim x gx


limitOfCauchySequenceIsLimit : ∀ x gx →
  isLimitSequence x (limitOfCauchySequence x gx)
limitOfCauchySequenceIsLimit = Real.Premetric.lim-isLimitSeq


limitOfCauchySequenceIndependent : ∀ x
  (gx gy : IsCauchySequence x) →
  limitOfCauchySequence x gx ≡
  limitOfCauchySequence x gy
limitOfCauchySequenceIndependent x gx gy =
  cong (Real.Base.lim x)
    (isPropIsCauchySequence x gx gy)


canonicalLimit≡ : ∀ x gx l →
  isLimitSequence x l →
  limitOfCauchySequence x gx ≡ l
canonicalLimit≡ x gx l x→l =
  cong fst
    (isPropSequenceLimit x
      (limitOfCauchySequence x gx ,
       limitOfCauchySequenceIsLimit x gx)
      (l , x→l))


-- A convergent sequence is radiuswise Cauchy.  Only the truncated tail at
-- `ε/2` is opened, and the result is again a propositionally truncated tail
-- at `ε`.  There is no attempt to choose these tails simultaneously.

isLimitSequence→isCauchySequence : ∀ {x l} →
  isLimitSequence x l → IsCauchySequence x
isLimitSequence→isCauchySequence {x} {l} x→l ε =
  PT.map to-cauchy-tail (x→l (ε /2₊))
  where
  to-cauchy-tail :
    Σ[ N ∈ ℕ ]
      (∀ n → N ℕ.≤ n → x n Real.Base.≈ᶜ[ ε /2₊ ] l) →
    CauchyTail x ε
  to-cauchy-tail (N , close) = N , λ m n N≤m N≤n →
    subst (λ ρ → x m Real.Base.≈ᶜ[ ρ ] x n)
      (ℚ₊≡ (/2+/2≡id (fst ε)))
      (Real.Approximation.tri≈ᶜ
        (x m) l (x n) (ε /2₊) (ε /2₊)
        (close m N≤m)
        (Real.Base.sym≈ᶜ (x n) l (ε /2₊) (close n N≤n)))


sequenceLimit→isCauchySequence : ∀ {x} →
  SequenceLimit x → IsCauchySequence x
sequenceLimit→isCauchySequence (_ , x→l) =
  isLimitSequence→isCauchySequence x→l


-- This is the useful strengthening supplied by the new completion.  A
-- radiuswise Cauchy sequence is equivalent to an actual convergent sequence,
-- even though it need not carry (or merely carry) one global modulus.

isCauchySequence≃sequenceLimit : ∀ x →
  IsCauchySequence x ≃ SequenceLimit x
isCauchySequence≃sequenceLimit x =
  propBiimpl→Equiv
    (isPropIsCauchySequence x)
    (isPropSequenceLimit x)
    (cauchySequenceLimit x)
    sequenceLimit→isCauchySequence


-- Continuity and radiuswise Cauchyness ----------------------------------
--
-- A continuous map does not preserve Cauchy sequences in every incomplete
-- space.  It does here because a radiuswise Cauchy sequence of reals first
-- acquires its unique limit.  Continuity preserves that limit, and every
-- convergent sequence is radiuswise Cauchy.

continuousPreservesIsLimitSequence :
  (f : Real.ℝ → Real.ℝ) →
  isContinuous
    (snd Real.ℝPremetricSpace) f
    (snd Real.ℝPremetricSpace) →
  ∀ {x l} → isLimitSequence x l →
  isLimitSequence (f ∘ x) (f l)
continuousPreservesIsLimitSequence f f-cont {x} {l} =
  C→seqContinuous
    {M = Real.ℝPremetricSpace}
    {N = Real.ℝPremetricSpace}
    (f , f-cont) x l


continuousPreservesIsCauchySequence :
  (f : Real.ℝ → Real.ℝ) →
  isContinuous
    (snd Real.ℝPremetricSpace) f
    (snd Real.ℝPremetricSpace) →
  ∀ x → IsCauchySequence x →
  IsCauchySequence (f ∘ x)
continuousPreservesIsCauchySequence f f-cont x gx =
  isLimitSequence→isCauchySequence
    (continuousPreservesIsLimitSequence f f-cont
      (limitOfCauchySequenceIsLimit x gx))


nonExpandingPresIsCauchySequence :
  (f : NE[ Real.ℝPremetricSpace , Real.ℝPremetricSpace ]) →
  ∀ x → IsCauchySequence x →
  IsCauchySequence (fst f ∘ x)
nonExpandingPresIsCauchySequence f =
  continuousPreservesIsCauchySequence
    (fst f) (snd (NE→C f))


nonExpandingPresIsLimitSequence :
  (f : NE[ Real.ℝPremetricSpace , Real.ℝPremetricSpace ]) →
  ∀ {x l} → isLimitSequence x l →
  isLimitSequence (fst f ∘ x) (fst f l)
nonExpandingPresIsLimitSequence f =
  continuousPreservesIsLimitSequence
    (fst f) (snd (NE→C f))


continuousBinaryPreservesIsLimitSequence :
  (f : Real.ℝ × Real.ℝ → Real.ℝ) →
  isContinuous
    (snd (PremetricProduct
      Real.ℝPremetricSpace Real.ℝPremetricSpace)) f
    (snd Real.ℝPremetricSpace) →
  ∀ {x y l m} →
  isLimitSequence x l → isLimitSequence y m →
  isLimitSequence (λ n → f (x n , y n)) (f (l , m))
continuousBinaryPreservesIsLimitSequence f f-cont
    {x} {y} {l} {m} x→l y→m =
  C→seqContinuous
    {M = PremetricProduct
      Real.ℝPremetricSpace Real.ℝPremetricSpace}
    {N = Real.ℝPremetricSpace}
    (f , f-cont)
    (λ n → x n , y n) (l , m)
    (pairPresIsLimitSeq
      {M = Real.ℝPremetricSpace}
      {N = Real.ℝPremetricSpace}
      x y l m x→l y→m)


continuousBinaryPreservesIsCauchySequence :
  (f : Real.ℝ × Real.ℝ → Real.ℝ) →
  isContinuous
    (snd (PremetricProduct
      Real.ℝPremetricSpace Real.ℝPremetricSpace)) f
    (snd Real.ℝPremetricSpace) →
  ∀ x y →
  IsCauchySequence x → IsCauchySequence y →
  IsCauchySequence (λ n → f (x n , y n))
continuousBinaryPreservesIsCauchySequence f f-cont x y gx gy =
  isLimitSequence→isCauchySequence
    (continuousBinaryPreservesIsLimitSequence f f-cont
      (limitOfCauchySequenceIsLimit x gx)
      (limitOfCauchySequenceIsLimit y gy))


-- Basic constructors and reindexing -------------------------------------

constantIsCauchySequence : ∀ x →
  IsCauchySequence (λ _ → x)
constantIsCauchySequence x ε =
  ∣ 0 , (λ _ _ _ _ → Real.Base.isRefl≈ᶜ x ε) ∣₁


constantIsLimitSequence : ∀ x →
  isLimitSequence (λ _ → x) x
constantIsLimitSequence x ε =
  ∣ 0 , (λ _ _ → Real.Base.isRefl≈ᶜ x ε) ∣₁


shiftSequence : ℕ → (ℕ → Real.ℝ) → ℕ → Real.ℝ
shiftSequence = Theory.shiftSeq


shiftPresIsCauchySequence : ∀ k x →
  IsCauchySequence x → IsCauchySequence (shiftSequence k x)
shiftPresIsCauchySequence k x gx ε =
  PT.map shift-tail (gx ε)
  where
  shift-tail : CauchyTail x ε →
    CauchyTail (shiftSequence k x) ε
  shift-tail (N , close) = N , λ m n N≤m N≤n →
    close (k ℕ.+ m) (k ℕ.+ n)
      (ℕ.≤-trans N≤m ℕ.≤SumRight)
      (ℕ.≤-trans N≤n ℕ.≤SumRight)


shiftPresIsLimitSequence : ∀ k x l →
  isLimitSequence x l →
  isLimitSequence (shiftSequence k x) l
shiftPresIsLimitSequence = Theory.shiftPresIsLimitSeq


shiftReflectsIsLimitSequence : ∀ k x l →
  isLimitSequence (shiftSequence k x) l →
  isLimitSequence x l
shiftReflectsIsLimitSequence = Theory.shiftReflectsIsLimitSeq


EventuallyEqualTail :
  (ℕ → Real.ℝ) → (ℕ → Real.ℝ) → Type₀
EventuallyEqualTail x y =
  Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → x n ≡ y n)


EventuallyEqualSequence :
  (ℕ → Real.ℝ) → (ℕ → Real.ℝ) → Type₀
EventuallyEqualSequence x y = ∥ EventuallyEqualTail x y ∥₁


isPropEventuallyEqualSequence : ∀ x y →
  isProp (EventuallyEqualSequence x y)
isPropEventuallyEqualSequence x y = squash₁


eventuallyEqualRefl : ∀ x → EventuallyEqualSequence x x
eventuallyEqualRefl x = ∣ 0 , (λ _ _ → refl) ∣₁


eventuallyEqualSym : ∀ {x y} →
  EventuallyEqualSequence x y → EventuallyEqualSequence y x
eventuallyEqualSym = PT.map λ where
  (N , equal) → N , λ n N≤n → sym (equal n N≤n)


eventuallyEqualPresIsCauchySequence : ∀ {x y} →
  EventuallyEqualSequence x y →
  IsCauchySequence x → IsCauchySequence y
eventuallyEqualPresIsCauchySequence {x} {y} merely-equal gx =
  PT.rec (isPropIsCauchySequence y) with-cutoff merely-equal
  where
  with-cutoff : EventuallyEqualTail x y → IsCauchySequence y
  with-cutoff (K , equal) ε = PT.map transport-tail (gx ε)
    where
    transport-tail : CauchyTail x ε → CauchyTail y ε
    transport-tail (N , close) =
      ℕ.max K N , λ m n max≤m max≤n →
        subst2 (Real.Base._≈ᶜ[ ε ]_)
          (equal m (ℕ.≤-trans
            (ℕ.left-≤-max {m = K} {n = N}) max≤m))
          (equal n (ℕ.≤-trans
            (ℕ.left-≤-max {m = K} {n = N}) max≤n))
          (close m n
            (ℕ.≤-trans
              (ℕ.right-≤-max {n = N} {m = K}) max≤m)
            (ℕ.≤-trans
              (ℕ.right-≤-max {n = N} {m = K}) max≤n))


eventuallyEqualPresIsLimitSequence : ∀ {x y l} →
  EventuallyEqualSequence x y →
  isLimitSequence x l → isLimitSequence y l
eventuallyEqualPresIsLimitSequence {x} {y} {l} merely-equal x→l =
  PT.rec (isPropIsLimitSequence y l)
    (λ equal →
      Theory.eventuallyEqualSeqPresIsLimitSeq x y l equal x→l)
    merely-equal


-- Asymptotic closeness ---------------------------------------------------
--
-- This relation follows the same truncation discipline as convergence and
-- Cauchyness: an appropriate tail exists separately at every radius.

EventuallyClose :
  (ℕ → Real.ℝ) → (ℕ → Real.ℝ) → Type₀
EventuallyClose x y = ∀ ε →
  ∃[ N ∈ ℕ ]
    (∀ n → N ℕ.≤ n → x n Real.Base.≈ᶜ[ ε ] y n)


isPropEventuallyClose : ∀ x y → isProp (EventuallyClose x y)
isPropEventuallyClose x y = isPropΠ λ _ → squash₁


eventuallyCloseRefl : ∀ x → EventuallyClose x x
eventuallyCloseRefl x ε =
  ∣ 0 , (λ n _ → Real.Base.isRefl≈ᶜ (x n) ε) ∣₁


eventuallyCloseSym : ∀ {x y} →
  EventuallyClose x y → EventuallyClose y x
eventuallyCloseSym {x} {y} close ε =
  PT.map
    (λ { (N , tail) →
      N , λ n N≤n →
        Real.Base.sym≈ᶜ (x n) (y n) ε (tail n N≤n) })
    (close ε)


eventuallyClosePresIsCauchySequence : ∀ {x y} →
  EventuallyClose x y →
  IsCauchySequence x → IsCauchySequence y
eventuallyClosePresIsCauchySequence {x} {y} close gx ε =
  PT.rec squash₁ with-source (gx (ε /2₊))
  where
  with-source : CauchyTail x (ε /2₊) →
    ∥ CauchyTail y ε ∥₁
  with-source (K , x-close) =
    PT.map with-error (close (ε /4₊))
    where
    with-error :
      (Σ[ L ∈ ℕ ]
        (∀ n → L ℕ.≤ n →
          x n Real.Base.≈ᶜ[ ε /4₊ ] y n)) →
      CauchyTail y ε
    with-error (L , error) =
      ℕ.max K L , λ m n max≤m max≤n →
        subst (λ ρ → y m Real.Base.≈ᶜ[ ρ ] y n)
          (ℚ₊≡ ℚ!)
          (Real.Approximation.tri≈ᶜ
            (y m) (x m) (y n) (ε /4₊) ((ε /2₊) +₊ (ε /4₊))
            (Real.Base.sym≈ᶜ (x m) (y m) (ε /4₊)
              (error m (ℕ.≤-trans
                (ℕ.right-≤-max {n = L} {m = K}) max≤m)))
            (Real.Approximation.tri≈ᶜ
              (x m) (x n) (y n) (ε /2₊) (ε /4₊)
              (x-close m n
                (ℕ.≤-trans
                  (ℕ.left-≤-max {m = K} {n = L}) max≤m)
                (ℕ.≤-trans
                  (ℕ.left-≤-max {m = K} {n = L}) max≤n))
              (error n (ℕ.≤-trans
                (ℕ.right-≤-max {n = L} {m = K}) max≤n))))


eventuallyClosePresIsLimitSequence : ∀ {x y l} →
  EventuallyClose x y →
  isLimitSequence x l → isLimitSequence y l
eventuallyClosePresIsLimitSequence {x} {y} {l} close x→l ε =
  PT.rec squash₁ with-limit (x→l (ε /2₊))
  where
  with-limit :
    (Σ[ K ∈ ℕ ]
      (∀ n → K ℕ.≤ n → x n Real.Base.≈ᶜ[ ε /2₊ ] l)) →
    ∃[ N ∈ ℕ ]
      (∀ n → N ℕ.≤ n → y n Real.Base.≈ᶜ[ ε ] l)
  with-limit (K , x-close) =
    PT.map with-error (close (ε /2₊))
    where
    with-error :
      (Σ[ L ∈ ℕ ]
        (∀ n → L ℕ.≤ n →
          x n Real.Base.≈ᶜ[ ε /2₊ ] y n)) →
      Σ[ N ∈ ℕ ]
        (∀ n → N ℕ.≤ n → y n Real.Base.≈ᶜ[ ε ] l)
    with-error (L , error) =
      ℕ.max K L , λ n max≤n →
        subst (λ ρ → y n Real.Base.≈ᶜ[ ρ ] l)
          (ℚ₊≡ (/2+/2≡id (fst ε)))
          (Real.Approximation.tri≈ᶜ
            (y n) (x n) l (ε /2₊) (ε /2₊)
            (Real.Base.sym≈ᶜ (x n) (y n) (ε /2₊)
              (error n (ℕ.≤-trans
                (ℕ.right-≤-max {n = L} {m = K}) max≤n)))
            (x-close n (ℕ.≤-trans
              (ℕ.left-≤-max {m = K} {n = L}) max≤n)))
