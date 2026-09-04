module Cubical.Analysis.Real.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Base
open import Cubical.Analysis.Real.Algebra.Lattice.Base
open import Cubical.Analysis.Real.Metric.Distance

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Instances.Rationals
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Instances.Product

import Cubical.Analysis.Completion.Limit as LimitDefinition
import Cubical.Analysis.Completion.BinaryLimit as BinaryLimitDefinition

private
  module Limit = LimitDefinition ℚPremetricSpace ℚPremetricSpace
  module BinaryLimit = BinaryLimitDefinition
    ℚPremetricSpace ℚPremetricSpace ℚPremetricSpace
  module RealBinary = BinaryNonExpanding
    ℝPremetricSpace ℝPremetricSpace ℝPremetricSpace
  module ℝTheory = PremetricTheory ℝPremetricSpace

  ℝ²PremetricSpace =
    PremetricProduct ℝPremetricSpace ℝPremetricSpace


-- Ordinary convergent sequences.  `SeqWitness` is the native input to the
-- completion constructor: a merely chosen global Cauchy modulus.

ChosenIsCauchySequence : (ℕ → ℝ) → Type₀
ChosenIsCauchySequence = ℝTheory.isCauchySeq

isLimitSequence : (ℕ → ℝ) → ℝ → Type₀
isLimitSequence = ℝTheory.isLimitSeq

isPropIsLimitSequence : ∀ x l →
  isProp (isLimitSequence x l)
isPropIsLimitSequence = ℝTheory.isPropIsLimitSeq

SequenceLimit : (ℕ → ℝ) → Type₀
SequenceLimit = ℝTheory.limitSeq

isPropSequenceLimit : ∀ x → isProp (SequenceLimit x)
isPropSequenceLimit = ℝTheory.isPropLimitSeq

opaque
  limitSequenceUnique : (sequence : ℕ → ℝ) (left right : ℝ) →
    isLimitSequence sequence left →
    isLimitSequence sequence right → left ≡ right
  limitSequenceUnique sequence left right left-limit right-limit =
    cong fst
      (isPropSequenceLimit sequence
        (left , left-limit) (right , right-limit))

sequenceLimit : ∀ x → SeqWitness x → SequenceLimit x
sequenceLimit x gx = lim x gx , lim-isLimitSeq x gx

limitOfSequence : ∀ x → SeqWitness x → ℝ
limitOfSequence x gx = lim x gx

limitOfSequenceIsLimit : ∀ x gx →
  isLimitSequence x (limitOfSequence x gx)
limitOfSequenceIsLimit = lim-isLimitSeq

limitOfSequenceIndependent : ∀ x
  (gx gy : SeqWitness x) →
  limitOfSequence x gx ≡ limitOfSequence x gy
limitOfSequenceIndependent x gx gy =
  cong fst
    (isPropSequenceLimit x
      (sequenceLimit x gx) (sequenceLimit x gy))

canonicalLimit≡ : ∀ x gx l →
  isLimitSequence x l →
  limitOfSequence x gx ≡ l
canonicalLimit≡ x gx l x→l =
  cong fst
    (isPropSequenceLimit x
      (sequenceLimit x gx) (l , x→l))


constantSeqWitness : ∀ x →
  SeqWitness (λ _ → x)
constantSeqWitness x =
  ∣ (λ _ → 0) ,
    (λ ε _ _ _ _ → refl∼ x ε) ∣₁

constantIsLimitSequence : ∀ x →
  isLimitSequence (λ _ → x) x
constantIsLimitSequence x ε =
  ∣ 0 , (λ _ _ → refl∼ x ε) ∣₁


continuousPreservesIsLimitSequence :
  (f : ℝ → ℝ) →
  isContinuous
    (ℝPremetricSpace .snd) f
    (ℝPremetricSpace .snd) →
  ∀ {x l} → isLimitSequence x l →
  isLimitSequence (f ∘ x) (f l)
continuousPreservesIsLimitSequence f f-cont =
  C→seqContinuous
    {M = ℝPremetricSpace} {N = ℝPremetricSpace}
    (f , f-cont) _ _


-- An opaque boundary for limits of maps with expensive continuity witnesses
-- (for example completed power series).
opaque
  continuousRealMapPreservesLimit :
    (function : ℝ → ℝ) →
    isContinuous
      (ℝPremetricSpace .snd) function (ℝPremetricSpace .snd) →
    ∀ {sequence limit} → isLimitSequence sequence limit →
    isLimitSequence (function ∘ sequence) (function limit)
  continuousRealMapPreservesLimit = continuousPreservesIsLimitSequence


continuousBinaryPreservesIsLimitSequence :
  (f : ℝ × ℝ → ℝ) →
  isContinuous (ℝ²PremetricSpace .snd) f
    (ℝPremetricSpace .snd) →
  ∀ {x y l m} →
  isLimitSequence x l → isLimitSequence y m →
  isLimitSequence (λ n → f (x n , y n)) (f (l , m))
continuousBinaryPreservesIsLimitSequence f f-cont
    {x} {y} {l} {m} x→l y→m =
  C→seqContinuous
    {M = ℝ²PremetricSpace} {N = ℝPremetricSpace}
    (f , f-cont)
    (λ n → x n , y n) (l , m)
    (pairPresIsLimitSeq
      {M = ℝPremetricSpace} {N = ℝPremetricSpace}
      x y l m x→l y→m)


addPresIsLimitSequence : ∀ {x y l m} →
  isLimitSequence x l → isLimitSequence y m →
  isLimitSequence (λ n → x n + y n) (l + m)
addPresIsLimitSequence =
  continuousBinaryPreservesIsLimitSequence
    (uncurry _+_)
    (addOfContinuousIsContinuous
      (ℝ²PremetricSpace .snd)
      fst snd (snd productFstC) (snd productSndC))


mulPresIsLimitSequence : ∀ {x y l m} →
  isLimitSequence x l → isLimitSequence y m →
  isLimitSequence (λ n → x n · y n) (l · m)
mulPresIsLimitSequence =
  continuousBinaryPreservesIsLimitSequence
    (uncurry _·_)
    (mulOfContinuousIsContinuous
      (ℝ²PremetricSpace .snd)
      fst snd (snd productFstC) (snd productSndC))


negPresIsLimitSequence : ∀ {x l} →
  isLimitSequence x l →
  isLimitSequence (-_ ∘ x) (- l)
negPresIsLimitSequence =
  continuousPreservesIsLimitSequence -_ neg-isContinuous


subPresIsLimitSequence : ∀ {x y l m} →
  isLimitSequence x l → isLimitSequence y m →
  isLimitSequence (λ n → x n - y n) (l - m)
subPresIsLimitSequence x→l y→m =
  addPresIsLimitSequence x→l
    (negPresIsLimitSequence y→m)


shiftSequence : ℕ → (ℕ → ℝ) → ℕ → ℝ
shiftSequence = ℝTheory.shiftSeq

shiftPresIsLimitSequence : ∀ k x l →
  isLimitSequence x l →
  isLimitSequence (shiftSequence k x) l
shiftPresIsLimitSequence = ℝTheory.shiftPresIsLimitSeq

shiftReflectsIsLimitSequence : ∀ k x l →
  isLimitSequence (shiftSequence k x) l →
  isLimitSequence x l
shiftReflectsIsLimitSequence = ℝTheory.shiftReflectsIsLimitSeq


opaque
  convergentSuccessiveDifferences→zero :
    (sequence : ℕ → ℝ) (limit : ℝ) →
    isLimitSequence sequence limit →
    isLimitSequence
      (λ n → shiftSequence 1 sequence n - sequence n) 0ℝ
  convergentSuccessiveDifferences→zero sequence limit sequence→limit =
    subst
      (isLimitSequence
        (λ n → shiftSequence 1 sequence n - sequence n))
      (subSelf limit)
      (subPresIsLimitSequence
        (shiftPresIsLimitSequence 1 sequence limit sequence→limit)
        sequence→limit)


negSeqWitness : ∀ {x} → SeqWitness x → SeqWitness (-_ ∘ x)
negSeqWitness = Limit.mapSeqWitnessNonExpanding
  (-_ , neg-isNonExpanding)

neg-lim : ∀ x gx →
  - lim x gx ≡ lim (-_ ∘ x) (negSeqWitness gx)
neg-lim = Limit.nonExpanding-map-lim
  (-_ , neg-isNonExpanding)

absSeqWitness : ∀ {x} → SeqWitness x → SeqWitness (absℝ ∘ x)
absSeqWitness = Limit.mapSeqWitnessNonExpanding
  (absℝ , abs-isNonExpanding)

abs-lim : ∀ x gx →
  absℝ (lim x gx) ≡ lim (absℝ ∘ x) (absSeqWitness gx)
abs-lim = Limit.nonExpanding-map-lim
  (absℝ , abs-isNonExpanding)

private
  addition₂ : RealBinary.NE₂[_,_,_]
  addition₂ .RealBinary.NE₂[_,_,_].fun = _+_
  addition₂ .RealBinary.NE₂[_,_,_].leftNE = add-isNonExpanding₁
  addition₂ .RealBinary.NE₂[_,_,_].rightNE = add-isNonExpanding₂

  distance₂ : RealBinary.NE₂[_,_,_]
  distance₂ .RealBinary.NE₂[_,_,_].fun = distanceℝ
  distance₂ .RealBinary.NE₂[_,_,_].leftNE = distance-isNonExpanding₁
  distance₂ .RealBinary.NE₂[_,_,_].rightNE = distance-isNonExpanding₂

  max₂ : RealBinary.NE₂[_,_,_]
  max₂ .RealBinary.NE₂[_,_,_].fun = maxℝ
  max₂ .RealBinary.NE₂[_,_,_].leftNE = max-isNonExpanding₁
  max₂ .RealBinary.NE₂[_,_,_].rightNE = max-isNonExpanding₂

  min₂ : RealBinary.NE₂[_,_,_]
  min₂ .RealBinary.NE₂[_,_,_].fun = minℝ
  min₂ .RealBinary.NE₂[_,_,_].leftNE = min-isNonExpanding₁
  min₂ .RealBinary.NE₂[_,_,_].rightNE = min-isNonExpanding₂


addSeqWitness : ∀ {x y} →
  SeqWitness x → SeqWitness y →
  SeqWitness (λ n → x n + y n)
addSeqWitness = BinaryLimit.mapPairSeqWitness addition₂

add-lim-lim : ∀ x gx y gy →
  lim x gx + lim y gy ≡
  lim (λ n → x n + y n) (addSeqWitness gx gy)
add-lim-lim =
  BinaryLimit.binaryNonExpanding-map-lim-lim addition₂

distanceSeqWitness : ∀ {x y} →
  SeqWitness x → SeqWitness y →
  SeqWitness (λ n → distanceℝ (x n) (y n))
distanceSeqWitness = BinaryLimit.mapPairSeqWitness distance₂

distance-lim-lim : ∀ x gx y gy →
  distanceℝ (lim x gx) (lim y gy) ≡
  lim (λ n → distanceℝ (x n) (y n))
    (distanceSeqWitness gx gy)
distance-lim-lim =
  BinaryLimit.binaryNonExpanding-map-lim-lim distance₂

maxSeqWitness : ∀ {x y} →
  SeqWitness x → SeqWitness y →
  SeqWitness (λ n → maxℝ (x n) (y n))
maxSeqWitness = BinaryLimit.mapPairSeqWitness max₂

max-lim-lim : ∀ x gx y gy →
  maxℝ (lim x gx) (lim y gy) ≡
  lim (λ n → maxℝ (x n) (y n)) (maxSeqWitness gx gy)
max-lim-lim =
  BinaryLimit.binaryNonExpanding-map-lim-lim max₂

minSeqWitness : ∀ {x y} →
  SeqWitness x → SeqWitness y →
  SeqWitness (λ n → minℝ (x n) (y n))
minSeqWitness = BinaryLimit.mapPairSeqWitness min₂

min-lim-lim : ∀ x gx y gy →
  minℝ (lim x gx) (lim y gy) ≡
  lim (λ n → minℝ (x n) (y n)) (minSeqWitness gx gy)
min-lim-lim =
  BinaryLimit.binaryNonExpanding-map-lim-lim min₂


-- Multiplication is not globally non-expanding, so its synchronized limit
-- rule retains the explicitly supplied image witness from the
-- completion-centered lift.

mul-lim-lim : ∀ x gx y gy imageWitness →
  lim x gx · lim y gy ≡
  lim (λ n → x n · y n) imageWitness
mul-lim-lim = multiplyℝ-lim-lim
