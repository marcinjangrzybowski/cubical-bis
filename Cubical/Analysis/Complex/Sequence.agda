module Cubical.Analysis.Complex.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric

ComplexSequence : Type₀
ComplexSequence = ℕ → ℂ

-- This is a pair of global native Cauchy witnesses, not a family of
-- radiuswise truncated tail bounds. Combining two witnesses is finite.
ComplexSeqWitness : ComplexSequence → Type₀
ComplexSeqWitness z = SeqWitness (re ∘ z) × SeqWitness (im ∘ z)

isPropComplexSeqWitness : ∀ z → isProp (ComplexSeqWitness z)
isPropComplexSeqWitness z = isProp× squash₁ squash₁

IsComplexLimit : ComplexSequence → ℂ → Type₀
IsComplexLimit z l = isLimitSequence (re ∘ z) (re l) × isLimitSequence (im ∘ z) (im l)

isPropIsComplexLimit : ∀ z l → isProp (IsComplexLimit z l)
isPropIsComplexLimit z l = isProp×
  (isPropIsLimitSequence (re ∘ z) (re l))
  (isPropIsLimitSequence (im ∘ z) (im l))

complexLimitUnique : ∀ z l m → IsComplexLimit z l → IsComplexLimit z m → l ≡ m
complexLimitUnique z l m zl zm = ℂ≡
  (limitSequenceUnique (re ∘ z) (re l) (re m) (fst zl) (fst zm))
  (limitSequenceUnique (im ∘ z) (im l) (im m) (snd zl) (snd zm))

limitℂ : (z : ComplexSequence) → ComplexSeqWitness z → ℂ
limitℂ z witness = lim (re ∘ z) (fst witness) , lim (im ∘ z) (snd witness)

limitℂ-isLimit : ∀ z witness → IsComplexLimit z (limitℂ z witness)
limitℂ-isLimit z witness = lim-isLimitSeq (re ∘ z) (fst witness) ,
  lim-isLimitSeq (im ∘ z) (snd witness)

complexLimit→premetricLimit : ∀ z l → IsComplexLimit z l →
  PremetricTheory.isLimitSeq ℂPremetricSpace z l
complexLimit→premetricLimit z l (r , i) =
  pairPresIsLimitSeq {M = ℝPremetricSpace} {N = ℝPremetricSpace}
    (re ∘ z) (im ∘ z) (re l) (im l) r i

premetricLimit→complexLimit : ∀ z l →
  PremetricTheory.isLimitSeq ℂPremetricSpace z l → IsComplexLimit z l
premetricLimit→complexLimit z l zl =
  (λ ε → PT.map (λ (N , tail) → N , λ n N≤n → fst (tail n N≤n)) (zl ε)) ,
  (λ ε → PT.map (λ (N , tail) → N , λ n N≤n → snd (tail n N≤n)) (zl ε))

chosenComplexCauchy→witness : ∀ z →
  PremetricTheory.isCauchySeq ℂPremetricSpace z → ComplexSeqWitness z
chosenComplexCauchy→witness z (N , tail) =
  ∣ N , (λ ε m n Nm Nn → fst (tail ε m n Nm Nn)) ∣₁ ,
  ∣ N , (λ ε m n Nm Nn → snd (tail ε m n Nm Nn)) ∣₁

complexWitness→mereCauchy : ∀ z → ComplexSeqWitness z →
  ∥ PremetricTheory.isCauchySeq ℂPremetricSpace z ∥₁
complexWitness→mereCauchy z (r , i) = PT.map2
  (pairPresIsCauchySeq {M = ℝPremetricSpace} {N = ℝPremetricSpace}
    (re ∘ z) (im ∘ z)) r i

constantComplexLimit : ∀ z → IsComplexLimit (λ _ → z) z
constantComplexLimit z = constantIsLimitSequence (re z) , constantIsLimitSequence (im z)

addComplexLimit : ∀ {z w l m} → IsComplexLimit z l → IsComplexLimit w m →
  IsComplexLimit (λ n → z n +ℂ w n) (l +ℂ m)
addComplexLimit (zr , zi) (wr , wi) = addPresIsLimitSequence zr wr , addPresIsLimitSequence zi wi

negComplexLimit : ∀ {z l} → IsComplexLimit z l →
  IsComplexLimit (λ n → -ℂ z n) (-ℂ l)
negComplexLimit (zr , zi) = negPresIsLimitSequence zr , negPresIsLimitSequence zi

subComplexLimit : ∀ {z w l m} → IsComplexLimit z l → IsComplexLimit w m →
  IsComplexLimit (λ n → z n -ℂ w n) (l -ℂ m)
subComplexLimit zl wm = addComplexLimit zl (negComplexLimit wm)

mulComplexLimit : ∀ {z w l m} → IsComplexLimit z l → IsComplexLimit w m →
  IsComplexLimit (λ n → z n ·ℂ w n) (l ·ℂ m)
mulComplexLimit (zr , zi) (wr , wi) =
  subPresIsLimitSequence (mulPresIsLimitSequence zr wr) (mulPresIsLimitSequence zi wi) ,
  addPresIsLimitSequence (mulPresIsLimitSequence zr wi) (mulPresIsLimitSequence zi wr)
