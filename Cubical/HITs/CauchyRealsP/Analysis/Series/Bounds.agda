module Cubical.HITs.CauchyRealsP.Analysis.Series.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ
  using (ℕ ; _∸_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sum using (inl ; inr)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Operations
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution

positiveRationalNonnegative : ∀ B →
  0 ≤ℝ rat (fst B)
positiveRationalNonnegative B =
  ≤ℚ→≤ℝ 0 (fst B)
    (ℚ.<Weaken≤ 0 (fst B) (snd B))

weakenUniformPartialSumAbsBound :
  ∀ B C terms →
  fst B ℚ.≤ fst C →
  UniformPartialSumAbsBound B terms →
  UniformPartialSumAbsBound C terms
weakenUniformPartialSumAbsBound
  B C terms B≤C bounded n =
    ≤ℝ-trans
      (absℝ (partialSum terms n))
      (rat (fst B))
      (rat (fst C))
      (bounded n)
      (≤ℚ→≤ℝ (fst B) (fst C) B≤C)

weakenUniformAbsolutePartialSumBound :
  ∀ B C terms →
  fst B ℚ.≤ fst C →
  UniformAbsolutePartialSumBound B terms →
  UniformAbsolutePartialSumBound C terms
weakenUniformAbsolutePartialSumBound
  B C terms B≤C bounded n =
    ≤ℝ-trans
      (partialSum (absℝ ∘ terms) n)
      (rat (fst B))
      (rat (fst C))
      (bounded n)
      (≤ℚ→≤ℝ (fst B) (fst C) B≤C)

FinitePrefixPartialSumAbsBound :
  ℕ → ℚ₊ → RealSequence → Type
FinitePrefixPartialSumAbsBound
  cutoff B terms =
    ∀ n →
    n ℕ.≤ cutoff →
    absℝ (partialSum terms n)
      ≤ℝ rat (fst B)

FinitePrefixAbsolutePartialSumBound :
  ℕ → ℚ₊ → RealSequence → Type
FinitePrefixAbsolutePartialSumBound
  cutoff B terms =
    ∀ n →
    n ℕ.≤ cutoff →
    partialSum (absℝ ∘ terms) n
      ≤ℝ rat (fst B)

UniformTailPartialSumAbsBound :
  ℕ → ℚ₊ → RealSequence → Type
UniformTailPartialSumAbsBound
  cutoff B terms =
    UniformPartialSumAbsBound
      B (dropSeries cutoff terms)

UniformAbsoluteTailPartialSumBound :
  ℕ → ℚ₊ → RealSequence → Type
UniformAbsoluteTailPartialSumBound
  cutoff B terms =
    UniformAbsolutePartialSumBound
      B (dropSeries cutoff terms)

prefixAndTailUniformPartialSumAbsBound :
  ∀ cutoff A B terms →
  FinitePrefixPartialSumAbsBound
    cutoff A terms →
  UniformTailPartialSumAbsBound
    cutoff B terms →
  UniformPartialSumAbsBound
    (A +₊ B) terms
prefixAndTailUniformPartialSumAbsBound
  cutoff A B terms
  prefix-bounded tail-bounded n
  with ℕ.Dichotomyℕ n cutoff
... | inl n≤cutoff =
  ≤ℝ-trans
    (absℝ (partialSum terms n))
    (rat (fst A))
    (rat (fst (A +₊ B)))
    (prefix-bounded n n≤cutoff)
    (≤ℚ→≤ℝ
      (fst A) (fst (A +₊ B))
      (ℚ.<Weaken≤
        (fst A) (fst (A +₊ B))
        (<₊SumLeft A B)))
... | inr cutoff<n =
  subst
    (absℝ (partialSum terms n) ≤ℝ_)
    (rat+rat (fst A) (fst B))
    (≤ℝ-trans
      (absℝ (partialSum terms n))
      ( absℝ (partialSum terms cutoff)
      + absℝ
          (partialSum
            (dropSeries cutoff terms)
            count)
      )
      (rat (fst A) + rat (fst B))
      split-triangle
      (≤ℝ-add
        (absℝ (partialSum terms cutoff))
        (rat (fst A))
        (absℝ
          (partialSum
            (dropSeries cutoff terms)
            count))
        (rat (fst B))
        (prefix-bounded
          cutoff ℕ.≤-refl)
        (tail-bounded count)))
  where
  cutoff≤n : cutoff ℕ.≤ n
  cutoff≤n =
    ℕ.<-weaken cutoff<n

  count : ℕ
  count =
    n ∸ cutoff

  count+cutoff≡n :
    count ℕ.+ cutoff ≡ n
  count+cutoff≡n =
    ℕ.≤-∸-+-cancel cutoff≤n

  split-path :
    partialSum terms n ≡
    partialSum terms cutoff
      + partialSum
          (dropSeries cutoff terms)
          count
  split-path =
    cong (partialSum terms)
      (sym count+cutoff≡n)
    ∙ partialSum-drop-recombine
        cutoff terms count

  split-triangle :
    absℝ (partialSum terms n)
      ≤ℝ
    absℝ (partialSum terms cutoff)
      + absℝ
          (partialSum
            (dropSeries cutoff terms)
            count)
  split-triangle =
    subst
      (_≤ℝ
        absℝ (partialSum terms cutoff)
          + absℝ
              (partialSum
                (dropSeries cutoff terms)
                count))
      (sym (cong absℝ split-path))
      (absTriangle
        (partialSum terms cutoff)
        (partialSum
          (dropSeries cutoff terms)
          count))

prefixAndTailUniformAbsolutePartialSumBound :
  ∀ cutoff A B terms →
  FinitePrefixAbsolutePartialSumBound
    cutoff A terms →
  UniformAbsoluteTailPartialSumBound
    cutoff B terms →
  UniformAbsolutePartialSumBound
    (A +₊ B) terms
prefixAndTailUniformAbsolutePartialSumBound
  cutoff A B terms
  prefix-bounded tail-bounded n
  with ℕ.Dichotomyℕ n cutoff
... | inl n≤cutoff =
  ≤ℝ-trans
    (partialSum (absℝ ∘ terms) n)
    (rat (fst A))
    (rat (fst (A +₊ B)))
    (prefix-bounded n n≤cutoff)
    (≤ℚ→≤ℝ
      (fst A) (fst (A +₊ B))
      (ℚ.<Weaken≤
        (fst A) (fst (A +₊ B))
        (<₊SumLeft A B)))
... | inr cutoff<n =
  subst
    (partialSum (absℝ ∘ terms) n ≤ℝ_)
    (rat+rat (fst A) (fst B))
    (subst
      (_≤ℝ
        rat (fst A) + rat (fst B))
      (sym split-path)
      (≤ℝ-add
        (partialSum
          (absℝ ∘ terms)
          cutoff)
        (rat (fst A))
        (partialSum
          (absℝ ∘
            dropSeries cutoff terms)
          count)
        (rat (fst B))
        (prefix-bounded
          cutoff ℕ.≤-refl)
        (tail-bounded count)))
  where
  cutoff≤n : cutoff ℕ.≤ n
  cutoff≤n =
    ℕ.<-weaken cutoff<n

  count : ℕ
  count =
    n ∸ cutoff

  count+cutoff≡n :
    count ℕ.+ cutoff ≡ n
  count+cutoff≡n =
    ℕ.≤-∸-+-cancel cutoff≤n

  split-path :
    partialSum (absℝ ∘ terms) n ≡
    partialSum (absℝ ∘ terms) cutoff
      + partialSum
          (absℝ ∘
            dropSeries cutoff terms)
          count
  split-path =
    cong
      (partialSum (absℝ ∘ terms))
      (sym count+cutoff≡n)
    ∙ partialSum-drop-recombine
        cutoff (absℝ ∘ terms) count

dropPresUniformAbsolutePartialSumBound :
  ∀ cutoff B terms →
  UniformAbsolutePartialSumBound B terms →
  UniformAbsoluteTailPartialSumBound
    cutoff B terms
dropPresUniformAbsolutePartialSumBound
  cutoff B terms bounded n =
    ≤ℝ-trans
      tail total
      (rat (fst B))
      tail≤total
      (bounded (n ℕ.+ cutoff))
  where
  prefix tail total : ℝ
  prefix =
    partialSum (absℝ ∘ terms) cutoff
  tail =
    partialSum
      (absℝ ∘ dropSeries cutoff terms)
      n
  total =
    partialSum
      (absℝ ∘ terms)
      (n ℕ.+ cutoff)

  prefix-nonnegative :
    0 ≤ℝ prefix
  prefix-nonnegative =
    partialSumNonnegative
      (absℝ ∘ terms)
      (λ k → absNonnegative (terms k))
      cutoff

  recombine :
    total ≡ prefix + tail
  recombine =
    partialSum-drop-recombine
      cutoff (absℝ ∘ terms) n

  tail≤total :
    tail ≤ℝ total
  tail≤total =
    subst2 _≤ℝ_
      (addIdL tail)
      (sym recombine)
      (≤ℝ-add
        0 prefix tail tail
        prefix-nonnegative
        (≤ℝ-refl tail))

dropPresUniformPartialSumAbsBound :
  ∀ cutoff B terms →
  UniformPartialSumAbsBound B terms →
  UniformTailPartialSumAbsBound
    cutoff (B +₊ B) terms
dropPresUniformPartialSumAbsBound
  cutoff B terms bounded n =
    subst
      (absℝ
        (partialSum
          (dropSeries cutoff terms)
          n)
        ≤ℝ_)
      (rat+rat (fst B) (fst B))
      (subst
        (_≤ℝ
          rat (fst B) + rat (fst B))
        (cong absℝ (sym tail-path))
        (≤ℝ-trans
          (absℝ (shifted - prefix))
          (absℝ shifted + absℝ prefix)
          (rat (fst B) + rat (fst B))
          (absSubTriangle shifted prefix)
          (≤ℝ-add
            (absℝ shifted) (rat (fst B))
            (absℝ prefix) (rat (fst B))
            (bounded (n ℕ.+ cutoff))
            (bounded cutoff))))
  where
  prefix shifted : ℝ
  prefix =
    partialSum terms cutoff
  shifted =
    partialSum terms (n ℕ.+ cutoff)

  tail-path :
    partialSum
        (dropSeries cutoff terms)
        n
      ≡
    shifted - prefix
  tail-path =
    partialSum-drop cutoff terms n

eventuallyEqualPresUniformAbsolutePartialSumBound :
  ∀ A B a b →
  (eventual : EventuallyEqualSeq a b) →
  FinitePrefixAbsolutePartialSumBound
    (fst eventual) B b →
  UniformAbsolutePartialSumBound A a →
  UniformAbsolutePartialSumBound
    (B +₊ A) b
eventuallyEqualPresUniformAbsolutePartialSumBound
  A B a b eventual@(cutoff , equal)
  prefix-bounded a-bounded =
    prefixAndTailUniformAbsolutePartialSumBound
      cutoff B A b
      prefix-bounded b-tail-bounded
  where
  a-tail-bounded :
    UniformAbsoluteTailPartialSumBound
      cutoff A a
  a-tail-bounded =
    dropPresUniformAbsolutePartialSumBound
      cutoff A a a-bounded

  tail-path : ∀ n →
    partialSum
      (absℝ ∘ dropSeries cutoff a)
      n
      ≡
    partialSum
      (absℝ ∘ dropSeries cutoff b)
      n
  tail-path =
    partialSum-pointwise
      (absℝ ∘ dropSeries cutoff a)
      (absℝ ∘ dropSeries cutoff b)
      (λ n →
        cong absℝ
          (equal
            (n ℕ.+ cutoff)
            ℕ.≤SumRight))

  b-tail-bounded :
    UniformAbsoluteTailPartialSumBound
      cutoff A b
  b-tail-bounded n =
    subst
      (_≤ℝ rat (fst A))
      (tail-path n)
      (a-tail-bounded n)

eventuallyEqualPresUniformPartialSumAbsBound :
  ∀ A B a b →
  (eventual : EventuallyEqualSeq a b) →
  FinitePrefixPartialSumAbsBound
    (fst eventual) B b →
  UniformPartialSumAbsBound A a →
  UniformPartialSumAbsBound
    (B +₊ (A +₊ A)) b
eventuallyEqualPresUniformPartialSumAbsBound
  A B a b eventual@(cutoff , equal)
  prefix-bounded a-bounded =
    prefixAndTailUniformPartialSumAbsBound
      cutoff B (A +₊ A) b
      prefix-bounded b-tail-bounded
  where
  a-tail-bounded :
    UniformTailPartialSumAbsBound
      cutoff (A +₊ A) a
  a-tail-bounded =
    dropPresUniformPartialSumAbsBound
      cutoff A a a-bounded

  tail-path : ∀ n →
    partialSum (dropSeries cutoff a) n
      ≡
    partialSum (dropSeries cutoff b) n
  tail-path =
    partialSum-pointwise
      (dropSeries cutoff a)
      (dropSeries cutoff b)
      (λ n →
        equal
          (n ℕ.+ cutoff)
          ℕ.≤SumRight)

  b-tail-bounded :
    UniformTailPartialSumAbsBound
      cutoff (A +₊ A) b
  b-tail-bounded n =
    subst
      (λ tail →
        absℝ tail
          ≤ℝ rat (fst (A +₊ A)))
      (tail-path n)
      (a-tail-bounded n)

addUniformPartialSumAbsBound :
  ∀ A B a b →
  UniformPartialSumAbsBound A a →
  UniformPartialSumAbsBound B b →
  UniformPartialSumAbsBound
    (A +₊ B)
    (λ n → a n + b n)
addUniformPartialSumAbsBound
  A B a b a-bounded b-bounded n =
    subst
      (absℝ
        (partialSum (λ k → a k + b k) n)
        ≤ℝ_)
      (rat+rat (fst A) (fst B))
      (≤ℝ-trans
        (absℝ
          (partialSum (λ k → a k + b k) n))
        ( absℝ (partialSum a n)
        + absℝ (partialSum b n)
        )
        (rat (fst A) + rat (fst B))
        sum-triangle
        (≤ℝ-add
          (absℝ (partialSum a n))
          (rat (fst A))
          (absℝ (partialSum b n))
          (rat (fst B))
          (a-bounded n)
          (b-bounded n)))
  where
  sum-triangle :
    absℝ
      (partialSum (λ k → a k + b k) n)
      ≤ℝ
    absℝ (partialSum a n)
      + absℝ (partialSum b n)
  sum-triangle =
    subst
      (_≤ℝ
        absℝ (partialSum a n)
          + absℝ (partialSum b n))
      (sym
        (cong absℝ
          (partialSum-add a b n)))
      (absTriangle
        (partialSum a n)
        (partialSum b n))

addUniformAbsolutePartialSumBound :
  ∀ A B a b →
  UniformAbsolutePartialSumBound A a →
  UniformAbsolutePartialSumBound B b →
  UniformAbsolutePartialSumBound
    (A +₊ B)
    (λ n → a n + b n)
addUniformAbsolutePartialSumBound
  A B a b a-bounded b-bounded n =
    subst
      (partialSum
        (absℝ ∘ (λ k → a k + b k))
        n
        ≤ℝ_)
      (rat+rat (fst A) (fst B))
      (≤ℝ-trans
        (partialSum
          (absℝ ∘ (λ k → a k + b k))
          n)
        ( partialSum (absℝ ∘ a) n
        + partialSum (absℝ ∘ b) n
        )
        (rat (fst A) + rat (fst B))
        termwise-triangle
        (≤ℝ-add
          (partialSum (absℝ ∘ a) n)
          (rat (fst A))
          (partialSum (absℝ ∘ b) n)
          (rat (fst B))
          (a-bounded n)
          (b-bounded n)))
  where
  termwise-triangle :
    partialSum
      (absℝ ∘ (λ k → a k + b k))
      n
      ≤ℝ
    partialSum (absℝ ∘ a) n
      + partialSum (absℝ ∘ b) n
  termwise-triangle =
    subst
      (partialSum
        (absℝ ∘ (λ k → a k + b k))
        n
        ≤ℝ_)
      (partialSum-add
        (absℝ ∘ a)
        (absℝ ∘ b)
        n)
      (partialSumMono
        (absℝ ∘ (λ k → a k + b k))
        (λ k → absℝ (a k) + absℝ (b k))
        (λ k → absTriangle (a k) (b k))
        n)

scaleUniformPartialSumAbsBound :
  ∀ C B c terms →
  absℝ c ≤ℝ rat (fst C) →
  UniformPartialSumAbsBound B terms →
  UniformPartialSumAbsBound
    (C ·₊ B)
    (scaleSeries c terms)
scaleUniformPartialSumAbsBound
  C B c terms c-bounded terms-bounded n =
    subst
      (_≤ℝ rat (fst (C ·₊ B)))
      (sym scaled-path)
      product-bound
  where
  scaled-path :
    absℝ
      (partialSum (scaleSeries c terms) n)
      ≡
    absℝ c · absℝ (partialSum terms n)
  scaled-path =
    cong absℝ
      (partialSum-scale c terms n)
    ∙ absMul c (partialSum terms n)

  product-bound :
    absℝ c · absℝ (partialSum terms n)
      ≤ℝ
    rat (fst (C ·₊ B))
  product-bound =
    subst
      (absℝ c · absℝ (partialSum terms n)
        ≤ℝ_)
      (mul-rat (fst C) (fst B))
      (mulMono≤
        (absℝ c)
        (rat (fst C))
        (absℝ (partialSum terms n))
        (rat (fst B))
        (positiveRationalNonnegative C)
        (absNonnegative
          (partialSum terms n))
        c-bounded
        (terms-bounded n))

scaleUniformAbsolutePartialSumBound :
  ∀ C B c terms →
  absℝ c ≤ℝ rat (fst C) →
  UniformAbsolutePartialSumBound B terms →
  UniformAbsolutePartialSumBound
    (C ·₊ B)
    (scaleSeries c terms)
scaleUniformAbsolutePartialSumBound
  C B c terms c-bounded terms-bounded n =
    subst
      (_≤ℝ rat (fst (C ·₊ B)))
      (sym scaled-path)
      product-bound
  where
  scaled-path :
    partialSum
      (absℝ ∘ scaleSeries c terms)
      n
      ≡
    absℝ c
      · partialSum (absℝ ∘ terms) n
  scaled-path =
    partialSum-pointwise
      (absℝ ∘ scaleSeries c terms)
      (scaleSeries
        (absℝ c)
        (absℝ ∘ terms))
      (λ k → absMul c (terms k))
      n
    ∙ partialSum-scale
        (absℝ c)
        (absℝ ∘ terms)
        n

  product-bound :
    absℝ c
      · partialSum (absℝ ∘ terms) n
      ≤ℝ
    rat (fst (C ·₊ B))
  product-bound =
    subst
      ( absℝ c
          · partialSum (absℝ ∘ terms) n
        ≤ℝ_
      )
      (mul-rat (fst C) (fst B))
      (mulMono≤
        (absℝ c)
        (rat (fst C))
        (partialSum (absℝ ∘ terms) n)
        (rat (fst B))
        (positiveRationalNonnegative C)
        (partialSumNonnegative
          (absℝ ∘ terms)
          (λ k → absNonnegative (terms k))
          n)
        c-bounded
        (terms-bounded n))
