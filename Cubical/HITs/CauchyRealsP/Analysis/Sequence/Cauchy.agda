module Cubical.HITs.CauchyRealsP.Analysis.Sequence.Cauchy where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
  using (ℕ)
  renaming (_+_ to _+ℕ_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

constantIsCauchySeq : ∀ x →
  isCauchySeq (λ _ → x)
constantIsCauchySeq x .fst _ =
  0
constantIsCauchySeq x .snd ε _ _ _ _ =
  refl∼ x ε

asymptoticallyCloseSeqPresIsCauchySeq :
  ∀ x y →
  AsymptoticallyCloseSeq x y →
  isCauchySeq x →
  isCauchySeq y
asymptoticallyCloseSeqPresIsCauchySeq
  x y close x-cauchy .fst ε =
    closeModulus ε +ℕ cauchyModulus ε
  where
  closeModulus : ℚ₊ → ℕ
  closeModulus δ =
    fst (close (δ /4₊))

  cauchyModulus : ℚ₊ → ℕ
  cauchyModulus δ =
    fst x-cauchy (δ /2₊)
asymptoticallyCloseSeqPresIsCauchySeq
  x y close x-cauchy
  .snd ε m n combined≤m combined≤n =
    subst∼
      (y m) (y n)
      {ε =
        (ε /4₊)
        +₊ ((ε /2₊) +₊ (ε /4₊))}
      {ε' = ε}
      ℚ!
      (triangle∼
        (y m) (x m) (y n)
        (ε /4₊)
        ((ε /2₊) +₊ (ε /4₊))
        (sym∼
          (x m) (y m) (ε /4₊)
          (eventuallyClose
            m
            (ℕ.≤-trans
              ℕ.≤SumLeft
              combined≤m)))
        (triangle∼
          (x m) (x n) (y n)
          (ε /2₊) (ε /4₊)
          (eventuallyCauchy
            m n
            (ℕ.≤-trans
              ℕ.≤SumRight
              combined≤m)
            (ℕ.≤-trans
              ℕ.≤SumRight
              combined≤n))
          (eventuallyClose
            n
            (ℕ.≤-trans
              ℕ.≤SumLeft
              combined≤n))))
  where
  closeModulus : ℕ
  closeModulus =
    fst (close (ε /4₊))

  cauchyModulus : ℕ
  cauchyModulus =
    fst x-cauchy (ε /2₊)

  eventuallyClose :
    ∀ n →
    closeModulus ℕ.≤ n →
    x n ∼[ ε /4₊ ] y n
  eventuallyClose =
    snd (close (ε /4₊))

  eventuallyCauchy :
    ∀ m n →
    cauchyModulus ℕ.≤ m →
    cauchyModulus ℕ.≤ n →
    x m ∼[ ε /2₊ ] x n
  eventuallyCauchy =
    snd x-cauchy (ε /2₊)

negPresIsCauchySeq : ∀ x →
  isCauchySeq x →
  isCauchySeq (λ n → - x n)
negPresIsCauchySeq =
  NE→presIsCauchySeq
    ((-_) , negIsNonExpanding)

absPresIsCauchySeq : ∀ x →
  isCauchySeq x →
  isCauchySeq (λ n → absℝ (x n))
absPresIsCauchySeq =
  NE→presIsCauchySeq
    (absℝ , absIsNonExpanding)

private
  realAddIsLipschitzWith2 :
    IsLipschitzWith
      (snd
        (PremetricProduct
          ℝPremetricSpace ℝPremetricSpace))
      (λ (x , y) → x + y)
      (snd ℝPremetricSpace)
      2
  realAddIsLipschitzWith2
    .IsLipschitzWith.pres≈
      (x , y) (x' , y') ε (x≈x' , y≈y') =
        subst∼
          (x + y) (x' + y')
          {ε = ε +₊ ε}
          {ε' = 2 ·₊ ε}
          ℚ!
          (addPres∼
            x x' y y' ε ε x≈x' y≈y')

  realMaxIsLipschitzWith2 :
    IsLipschitzWith
      (snd
        (PremetricProduct
          ℝPremetricSpace ℝPremetricSpace))
      (λ (x , y) → maxℝ x y)
      (snd ℝPremetricSpace)
      2
  realMaxIsLipschitzWith2
    .IsLipschitzWith.pres≈
      (x , y) (x' , y') ε (x≈x' , y≈y') =
        subst∼
          (maxℝ x y) (maxℝ x' y')
          {ε = ε +₊ ε}
          {ε' = 2 ·₊ ε}
          ℚ!
          (maxPres∼
            x x' y y' ε ε x≈x' y≈y')

addPresIsCauchySeq : ∀ x y →
  isCauchySeq x →
  isCauchySeq y →
  isCauchySeq (λ n → x n + y n)
addPresIsCauchySeq x y x-cauchy y-cauchy =
  LWith→presIsCauchySeq
    2
    (λ (x , y) → x + y)
    realAddIsLipschitzWith2
    (λ n → x n , y n)
    (pairPresIsCauchySeq
      {M = ℝPremetricSpace}
      {N = ℝPremetricSpace}
      x y x-cauchy y-cauchy)

subPresIsCauchySeq : ∀ x y →
  isCauchySeq x →
  isCauchySeq y →
  isCauchySeq (λ n → x n - y n)
subPresIsCauchySeq x y x-cauchy y-cauchy =
  addPresIsCauchySeq
    x (λ n → - y n)
    x-cauchy
    (negPresIsCauchySeq y y-cauchy)

maxPresIsCauchySeq : ∀ x y →
  isCauchySeq x →
  isCauchySeq y →
  isCauchySeq (λ n → maxℝ (x n) (y n))
maxPresIsCauchySeq x y x-cauchy y-cauchy =
  LWith→presIsCauchySeq
    2
    (λ (x , y) → maxℝ x y)
    realMaxIsLipschitzWith2
    (λ n → x n , y n)
    (pairPresIsCauchySeq
      {M = ℝPremetricSpace}
      {N = ℝPremetricSpace}
      x y x-cauchy y-cauchy)

minPresIsCauchySeq : ∀ x y →
  isCauchySeq x →
  isCauchySeq y →
  isCauchySeq (λ n → minℝ (x n) (y n))
minPresIsCauchySeq x y x-cauchy y-cauchy =
  negPresIsCauchySeq
    (λ n → maxℝ (- x n) (- y n))
    (maxPresIsCauchySeq
      (λ n → - x n) (λ n → - y n)
      (negPresIsCauchySeq x x-cauchy)
      (negPresIsCauchySeq y y-cauchy))

boundedMulPresIsCauchySeq : ∀ B x y →
  (∀ n → absℝ (x n) ≤ℝ rat (fst B)) →
  (∀ n → absℝ (y n) ≤ℝ rat (fst B)) →
  isCauchySeq x →
  isCauchySeq y →
  isCauchySeq (λ n → x n · y n)
boundedMulPresIsCauchySeq
  B x y x-bounded y-bounded x-cauchy y-cauchy
  .fst ε =
    fst pairedCauchy ((ε /2₊) ₊／₊ B)
  where
  pairedCauchy =
    pairPresIsCauchySeq
      {M = ℝPremetricSpace}
      {N = ℝPremetricSpace}
      x y x-cauchy y-cauchy
boundedMulPresIsCauchySeq
  B x y x-bounded y-bounded x-cauchy y-cauchy
  .snd ε m n modulus≤m modulus≤n =
    subst∼
      (x m · y m) (x n · y n)
      {ε = (ε /2₊) +₊ (ε /2₊)}
      {ε' = ε}
      (1/2∈ℚ./2+/2≡id (fst ε))
      (triangle∼
        (x m · y m) (x n · y m) (x n · y n)
        (ε /2₊) (ε /2₊)
        firstHalf secondHalf)
  where
  pairedCauchy =
    pairPresIsCauchySeq
      {M = ℝPremetricSpace}
      {N = ℝPremetricSpace}
      x y x-cauchy y-cauchy

  inputRadius : ℚ₊
  inputRadius =
    (ε /2₊) ₊／₊ B

  pairClose :
    (x m ∼[ inputRadius ] x n)
    × (y m ∼[ inputRadius ] y n)
  pairClose =
    snd pairedCauchy
      inputRadius m n modulus≤m modulus≤n

  firstHalf :
    (x m · y m) ∼[ ε /2₊ ] (x n · y m)
  firstHalf =
    subst∼
      (x m · y m) (x n · y m)
      {ε = B ·₊ inputRadius}
      {ε' = ε /2₊}
      (·／ B (ε /2₊))
      (IsLipschitzWith.pres≈
        (mulIsLipschitzRAtBound
          B (y m) (y-bounded m))
        (x m) (x n) inputRadius
        (fst pairClose))

  secondHalf :
    (x n · y m) ∼[ ε /2₊ ] (x n · y n)
  secondHalf =
    subst∼
      (x n · y m) (x n · y n)
      {ε = B ·₊ inputRadius}
      {ε' = ε /2₊}
      (·／ B (ε /2₊))
      (IsLipschitzWith.pres≈
        (mulIsLipschitzLAtBound
          B (x n) (x-bounded n))
        (y m) (y n) inputRadius
        (snd pairClose))

rationalScalePresIsCauchySeq :
  ∀ q x →
  isCauchySeq x →
  isCauchySeq (λ n → rat q · x n)
rationalScalePresIsCauchySeq q x x-cauchy =
  LWith→presIsCauchySeq
    scaleBound
    (rat q ·_)
    (mulIsLipschitzLAtBound
      scaleBound (rat q) absRat≤bound)
    x x-cauchy
  where
  scaleBound : ℚ₊
  scaleBound =
    ℚ.maxWithPos
      (1 , ℚ.0<sucN 0)
      (abs q)

  absRat≤bound :
    absℝ (rat q) ≤ℝ rat (fst scaleBound)
  absRat≤bound =
    subst
      (_≤ℝ rat (fst scaleBound))
      (sym (abs-rat q))
      (≤ℚ→≤ℝ
        (abs q) (fst scaleBound)
        (ℚ.≤max'
          1 (abs q)))
