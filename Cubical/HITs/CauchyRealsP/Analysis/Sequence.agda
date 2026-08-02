module Cubical.HITs.CauchyRealsP.Analysis.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
  using (ℕ)
  renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.PropositionalTruncation.Monad
import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Instances.Product

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open PremetricTheory ℝPremetricSpace public
  using
    ( isCauchySeq
    ; isCauchySeq<
    ; EventuallyEqualSeq
    ; eventuallyEqualSeqRefl
    ; eventuallyEqualSeqSym
    ; eventuallyEqualSeqPresIsCauchySeq
    ; isCauchySeq<→isCauchySeq
    ; isCauchySeq→isCauchySeq<
    ; isLimitSeq
    ; isPropIsLimitSeq
    ; limitSeq
    ; isPropLimitSeq
    ; eventuallyEqualSeqPresIsLimitSeq
    ; shiftSeq
    ; shiftPresIsCauchySeq
    ; shiftPresIsLimitSeq
    ; shiftReflectsIsLimitSeq
    )

private
  module ℝSequence = PremetricTheory ℝPremetricSpace

cauchySequenceLimit : ∀ x →
  isCauchySeq x →
  limitSeq x
cauchySequenceLimit x x-cauchy =
  limitPoint , sequenceLimit
  where
  modulus : ℚ₊ → ℕ
  modulus =
    fst x-cauchy

  eventuallyClose : ∀ ε m n →
    modulus ε ℕ.≤ m →
    modulus ε ℕ.≤ n →
    x m ∼[ ε ] x n
  eventuallyClose =
    snd x-cauchy

  approximation : ℚ₊ → ℝ
  approximation ε =
    x (modulus ε)

  approximationIsCauchy : ℝSequence.isCauchy approximation
  approximationIsCauchy =
    snd (ℝSequence.isCauchySeq→isCauchy x x-cauchy)

  completionLimit : ℝSequence.limit approximation
  completionLimit =
    isCompleteℝ approximation approximationIsCauchy

  limitPoint : ℝ
  limitPoint =
    fst completionLimit

  approximationLimit :
    ℝSequence.isLimit approximation limitPoint
  approximationLimit =
    snd completionLimit

  sequenceLimit : isLimitSeq x limitPoint
  sequenceLimit ε =
    return
      ( modulus (ε /4₊)
      , λ n modulus≤n →
          subst∼
            (x n) limitPoint
            {ε =
              (ε /4₊)
              +₊ ((ε /4₊) +₊ (ε /2₊))}
            {ε' = ε}
            ℚ!
            (triangle∼
              (x n)
              (x (modulus (ε /4₊)))
              limitPoint
              (ε /4₊)
              ((ε /4₊) +₊ (ε /2₊))
              (eventuallyClose
                (ε /4₊)
                n (modulus (ε /4₊))
                modulus≤n ℕ.≤-refl)
              (approximationLimit
                (ε /4₊) (ε /2₊)))
      )

limitOfCauchySequence : ∀ x →
  isCauchySeq x →
  ℝ
limitOfCauchySequence x x-cauchy =
  fst (cauchySequenceLimit x x-cauchy)

limitOfCauchySequenceIsLimit : ∀ x x-cauchy →
  isLimitSeq x (limitOfCauchySequence x x-cauchy)
limitOfCauchySequenceIsLimit x x-cauchy =
  snd (cauchySequenceLimit x x-cauchy)

limitOfCauchySequenceIndependent : ∀ x
  (p q : isCauchySeq x) →
  limitOfCauchySequence x p ≡
  limitOfCauchySequence x q
limitOfCauchySequenceIndependent x p q =
  cong fst
    (isPropLimitSeq x
      (cauchySequenceLimit x p)
      (cauchySequenceLimit x q))

constantIsLimitSeq : ∀ x →
  isLimitSeq (λ _ → x) x
constantIsLimitSeq x ε =
  return
    ( 0
    , λ _ _ → refl∼ x ε
    )

continuousPreservesIsLimitSeq :
  (f : ℝ → ℝ) →
  isContinuous
    (snd ℝPremetricSpace) f
    (snd ℝPremetricSpace) →
  ∀ x l →
  isLimitSeq x l →
  isLimitSeq (f ∘ x) (f l)
continuousPreservesIsLimitSeq f f-cont =
  C→seqContinuous (f , f-cont)

negPresIsLimitSeq : ∀ x l →
  isLimitSeq x l →
  isLimitSeq (λ n → - x n) (- l)
negPresIsLimitSeq =
  NE→seqContinuous
    ((-_) , negIsNonExpanding)

absPresIsLimitSeq : ∀ x l →
  isLimitSeq x l →
  isLimitSeq (λ n → absℝ (x n)) (absℝ l)
absPresIsLimitSeq =
  NE→seqContinuous
    (absℝ , absIsNonExpanding)

absLimitZeroReflects : ∀ x →
  isLimitSeq (λ n → absℝ (x n)) 0 →
  isLimitSeq x 0
absLimitZeroReflects x abs-limit ε =
  PT.map
    (λ (N , eventually-close) →
      N
      , λ n N≤n →
          absDifference<→closeness
            (x n) 0 ε
            (subst
              (_<ℝ rat (fst ε))
              source≡target
              (closeness→absDifference<
                (absℝ (x n)) 0 ε
                (eventually-close n N≤n))))
    (abs-limit ε)
  where
  source≡target : ∀ {n} →
    absℝ (absℝ (x n) - 0) ≡
    absℝ (x n - 0)
  source≡target {n} =
    cong absℝ (subZeroR (absℝ (x n)))
    ∙ absIdem (x n)
    ∙ cong absℝ (sym (subZeroR (x n)))

private
  realAddC :
    C[
      PremetricProduct ℝPremetricSpace ℝPremetricSpace
    , ℝPremetricSpace
    ]
  fst realAddC (x , y) =
    x + y
  snd realAddC =
    addOfContinuousIsContinuous
      (snd
        (PremetricProduct
          ℝPremetricSpace ℝPremetricSpace))
      fst snd
      (snd
        (productFstC
          {M = ℝPremetricSpace}
          {N = ℝPremetricSpace}))
      (snd
        (productSndC
          {M = ℝPremetricSpace}
          {N = ℝPremetricSpace}))

  realMulC :
    C[
      PremetricProduct ℝPremetricSpace ℝPremetricSpace
    , ℝPremetricSpace
    ]
  fst realMulC (x , y) =
    x · y
  snd realMulC =
    mulOfContinuousIsContinuous
      (snd
        (PremetricProduct
          ℝPremetricSpace ℝPremetricSpace))
      fst snd
      (snd
        (productFstC
          {M = ℝPremetricSpace}
          {N = ℝPremetricSpace}))
      (snd
        (productSndC
          {M = ℝPremetricSpace}
          {N = ℝPremetricSpace}))

  realMaxC :
    C[
      PremetricProduct ℝPremetricSpace ℝPremetricSpace
    , ℝPremetricSpace
    ]
  fst realMaxC (x , y) =
    maxℝ x y
  snd realMaxC =
    maxOfContinuousIsContinuous
      (snd
        (PremetricProduct
          ℝPremetricSpace ℝPremetricSpace))
      fst snd
      (snd
        (productFstC
          {M = ℝPremetricSpace}
          {N = ℝPremetricSpace}))
      (snd
        (productSndC
          {M = ℝPremetricSpace}
          {N = ℝPremetricSpace}))

addPresIsLimitSeq : ∀ x y l m →
  isLimitSeq x l →
  isLimitSeq y m →
  isLimitSeq (λ n → x n + y n) (l + m)
addPresIsLimitSeq x y l m x-lim y-lim =
  C→seqContinuous
    realAddC
    (λ n → x n , y n)
    (l , m)
    (pairPresIsLimitSeq
      {M = ℝPremetricSpace}
      {N = ℝPremetricSpace}
      x y l m x-lim y-lim)

subPresIsLimitSeq : ∀ x y l m →
  isLimitSeq x l →
  isLimitSeq y m →
  isLimitSeq (λ n → x n - y n) (l - m)
subPresIsLimitSeq x y l m x-lim y-lim =
  addPresIsLimitSeq
    x (λ n → - y n)
    l (- m)
    x-lim
    (negPresIsLimitSeq y m y-lim)

mulPresIsLimitSeq : ∀ x y l m →
  isLimitSeq x l →
  isLimitSeq y m →
  isLimitSeq (λ n → x n · y n) (l · m)
mulPresIsLimitSeq x y l m x-lim y-lim =
  C→seqContinuous
    realMulC
    (λ n → x n , y n)
    (l , m)
    (pairPresIsLimitSeq
      {M = ℝPremetricSpace}
      {N = ℝPremetricSpace}
      x y l m x-lim y-lim)

maxPresIsLimitSeq : ∀ x y l m →
  isLimitSeq x l →
  isLimitSeq y m →
  isLimitSeq
    (λ n → maxℝ (x n) (y n))
    (maxℝ l m)
maxPresIsLimitSeq x y l m x-lim y-lim =
  C→seqContinuous
    realMaxC
    (λ n → x n , y n)
    (l , m)
    (pairPresIsLimitSeq
      {M = ℝPremetricSpace}
      {N = ℝPremetricSpace}
      x y l m x-lim y-lim)

EventuallyLeSeq : (ℕ → ℝ) → (ℕ → ℝ) → Type
EventuallyLeSeq x y =
  Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → x n ≤ℝ y n)

eventuallyLeSeqPresLimit : ∀ x y l m →
  EventuallyLeSeq x y →
  isLimitSeq x l →
  isLimitSeq y m →
  l ≤ℝ m
eventuallyLeSeqPresLimit
  x y l m (N , eventually≤) x-lim y-lim =
    maxPath→≤ℝ l m maxLimit≡m
  where
  maxSequence : ℕ → ℝ
  maxSequence n =
    maxℝ (x n) (y n)

  maxSequenceEventuallyY :
    EventuallyEqualSeq maxSequence y
  maxSequenceEventuallyY =
    N , λ n N≤n →
      maxOf≤ (x n) (y n) (eventually≤ n N≤n)

  maxLimit :
    isLimitSeq maxSequence (maxℝ l m)
  maxLimit =
    maxPresIsLimitSeq x y l m x-lim y-lim

  yHasMaxLimit :
    isLimitSeq y (maxℝ l m)
  yHasMaxLimit =
    eventuallyEqualSeqPresIsLimitSeq
      maxSequence y (maxℝ l m)
      maxSequenceEventuallyY maxLimit

  maxLimit≡m : maxℝ l m ≡ m
  maxLimit≡m =
    cong fst
      (isPropLimitSeq y
        (maxℝ l m , yHasMaxLimit)
        (m , y-lim))

pointwiseLeSeqPresLimit : ∀ x y l m →
  (∀ n → x n ≤ℝ y n) →
  isLimitSeq x l →
  isLimitSeq y m →
  l ≤ℝ m
pointwiseLeSeqPresLimit x y l m pointwise≤ =
  eventuallyLeSeqPresLimit
    x y l m
    (0 , λ n _ → pointwise≤ n)

AsymptoticallyCloseSeq :
  (ℕ → ℝ) → (ℕ → ℝ) → Type
AsymptoticallyCloseSeq x y =
  ∀ ε →
  Σ[ N ∈ ℕ ]
    (∀ n → N ℕ.≤ n → x n ∼[ ε ] y n)

asymptoticallyCloseSeqSym : ∀ x y →
  AsymptoticallyCloseSeq x y →
  AsymptoticallyCloseSeq y x
asymptoticallyCloseSeqSym x y close ε =
  fst (close ε)
  , λ n modulus≤n →
      sym∼
        (x n) (y n) ε
        (snd (close ε) n modulus≤n)

asymptoticallyCloseSeqPresIsLimitSeq :
  ∀ x y l →
  AsymptoticallyCloseSeq x y →
  isLimitSeq x l →
  isLimitSeq y l
asymptoticallyCloseSeqPresIsLimitSeq
  x y l close x-lim ε =
    PT.map
      (λ (limitModulus , eventuallyLimit) →
        closeModulus +ℕ limitModulus
        , λ n combined≤n →
            subst∼
              (y n) l
              {ε = ε /2₊ +₊ ε /2₊}
              {ε' = ε}
              (1/2∈ℚ./2+/2≡id (fst ε))
              (triangle∼
                (y n) (x n) l
                (ε /2₊) (ε /2₊)
                (sym∼
                  (x n) (y n) (ε /2₊)
                  (eventuallyClose
                    n
                    (ℕ.≤-trans
                      ℕ.≤SumLeft
                      combined≤n)))
                (eventuallyLimit
                  n
                  (ℕ.≤-trans
                    ℕ.≤SumRight
                    combined≤n))))
      (x-lim (ε /2₊))
  where
  closeModulus : ℕ
  closeModulus =
    fst (close (ε /2₊))

  eventuallyClose :
    ∀ n →
    closeModulus ℕ.≤ n →
    x n ∼[ ε /2₊ ] y n
  eventuallyClose =
    snd (close (ε /2₊))

evaluatePolynomialPresIsLimitSeq : ∀ coefficients x l →
  isLimitSeq x l →
  isLimitSeq
    (λ n → evaluatePolynomial coefficients (x n))
    (evaluatePolynomial coefficients l)
evaluatePolynomialPresIsLimitSeq coefficients =
  continuousPreservesIsLimitSeq
    (evaluatePolynomial coefficients)
    (evaluatePolynomialIsContinuous coefficients)
