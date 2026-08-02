module Cubical.HITs.CauchyRealsP.Analysis.Series.Rational where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
  using (ℕ ; zero ; suc)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution

RationalSequence : Type
RationalSequence =
  ℕ → ℚ

ratSequence :
  RationalSequence → RealSequence
ratSequence terms n =
  rat (terms n)

rationalPartialSum :
  RationalSequence → ℕ → ℚ
rationalPartialSum terms zero =
  0
rationalPartialSum terms (suc n) =
  rationalPartialSum terms n
    ℚ.+ terms n

partialSum-ratSequence :
  ∀ terms n →
  partialSum (ratSequence terms) n
    ≡
  rat (rationalPartialSum terms n)
partialSum-ratSequence terms zero =
  refl
partialSum-ratSequence terms (suc n) =
  cong
      (_+ rat (terms n))
      (partialSum-ratSequence terms n)
  ∙ rat+rat
      (rationalPartialSum terms n)
      (terms n)

partialSum-absolute-ratSequence :
  ∀ terms n →
  partialSum
      (absℝ ∘ ratSequence terms)
      n
    ≡
  rat
    (rationalPartialSum
      (abs ∘ terms) n)
partialSum-absolute-ratSequence
  terms n =
    partialSum-pointwise
      (absℝ ∘ ratSequence terms)
      (ratSequence (abs ∘ terms))
      (λ k → abs-rat (terms k))
      n
    ∙ partialSum-ratSequence
        (abs ∘ terms) n

RationalUniformPartialSumAbsBound :
  ℚ₊ → RationalSequence → Type
RationalUniformPartialSumAbsBound
  B terms =
    ∀ n →
    abs (rationalPartialSum terms n)
      ℚ.≤ fst B

RationalUniformAbsolutePartialSumBound :
  ℚ₊ → RationalSequence → Type
RationalUniformAbsolutePartialSumBound
  B terms =
    ∀ n →
    rationalPartialSum
      (abs ∘ terms) n
      ℚ.≤ fst B

rationalUniformPartialSumAbsBound→real :
  ∀ B terms →
  RationalUniformPartialSumAbsBound
    B terms →
  UniformPartialSumAbsBound
    B (ratSequence terms)
rationalUniformPartialSumAbsBound→real
  B terms bounded n =
    subst
      (_≤ℝ rat (fst B))
      (sym partial-absolute-path)
      (≤ℚ→≤ℝ
        (abs (rationalPartialSum terms n))
        (fst B)
        (bounded n))
  where
  partial-absolute-path :
    absℝ
      (partialSum (ratSequence terms) n)
      ≡
    rat
      (abs
        (rationalPartialSum terms n))
  partial-absolute-path =
    cong absℝ
      (partialSum-ratSequence terms n)
    ∙ abs-rat
        (rationalPartialSum terms n)

rationalUniformAbsolutePartialSumBound→real :
  ∀ B terms →
  RationalUniformAbsolutePartialSumBound
    B terms →
  UniformAbsolutePartialSumBound
    B (ratSequence terms)
rationalUniformAbsolutePartialSumBound→real
  B terms bounded n =
    subst
      (_≤ℝ rat (fst B))
      (sym
        (partialSum-absolute-ratSequence
          terms n))
      (≤ℚ→≤ℝ
        (rationalPartialSum
          (abs ∘ terms) n)
        (fst B)
        (bounded n))
