module Cubical.Analysis.Real.Series.Product.AbsoluteNative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv using (invEq)

open import Cubical.Data.Nat as ℕ using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Bounds
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.NativeBounds
open import Cubical.Analysis.Real.Series.Product.Finite
open import Cubical.Analysis.Real.Series.Product.Convergence

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ


private
  module Pℝ = PremetricStr (ℝPremetricSpace .snd)
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  ≤ℚ→≤ℝ : ∀ p q → p ℚ.≤ q → rat p ≤ℝ rat q
  ≤ℚ→≤ℝ p q = invEq (rat≤rat≃ p q)


absoluteTerms-idempotent : ∀ (terms : RealSequence) →
  (absℝ ∘ (absℝ ∘ terms)) ≡ (absℝ ∘ terms)
absoluteTerms-idempotent terms =
  funExt (λ n → absIdem (terms n))


absoluteSequenceChosenIsAbsolutelyCauchy : ∀ (terms : RealSequence) →
  ChosenIsCauchySequence (partialSum (absℝ ∘ terms)) →
  ChosenIsCauchySequence
    (partialSum (absℝ ∘ (absℝ ∘ terms)))
absoluteSequenceChosenIsAbsolutelyCauchy terms =
  subst ChosenIsCauchySequence
    (sym
      (cong partialSum (absoluteTerms-idempotent terms)))


absoluteSequencePresUniformAbsoluteBound :
  ∀ (bound : ℚ₊) (terms : RealSequence) →
  UniformAbsolutePartialSumBound bound terms →
  UniformAbsolutePartialSumBound bound (absℝ ∘ terms)
absoluteSequencePresUniformAbsoluteBound bound terms bounded n =
  subst
    (_≤ℝ rat (fst bound))
    (sym
      (partialSum-pointwise
        (absℝ ∘ (absℝ ∘ terms))
        (absℝ ∘ terms)
        (λ k → absIdem (terms k)) n))
    (bounded n)


absolutePartialSumBound→absoluteSequenceBound :
  ∀ (bound : ℚ₊) (terms : RealSequence) →
  UniformAbsolutePartialSumBound bound terms →
  UniformPartialSumAbsBound bound (absℝ ∘ terms)
absolutePartialSumBound→absoluteSequenceBound bound terms bounded n =
  subst
    (_≤ℝ rat (fst bound))
    (sym
      (absOfNonnegative
        (partialSum (absℝ ∘ terms) n)
        (partialSumNonnegative
          (absℝ ∘ terms)
          (λ k → absNonnegative (terms k)) n)))
    (bounded n)


private
  productDifferencePath : ∀ x x' y y' →
    x · y - x' · y' ≡
    (x - x') · y + x' · (y - y')
  productDifferencePath x x' y y' =
    cong (x · y +_)
      (sym (addIdL (- (x' · y'))))
    ∙ cong
        (λ value → x · y + (value + (- (x' · y'))))
        (sym (addInvL (x' · y)))
    ∙ addAssoc (x · y) ((- (x' · y)) + x' · y) (- (x' · y'))
    ∙ cong (_+ (- (x' · y')))
        (addAssoc (x · y) (- (x' · y)) (x' · y))
    ∙ sym
        (addAssoc
          (x · y + (- (x' · y)))
          (x' · y) (- (x' · y')))
    ∙ cong₂ _+_
        (sym (ℝRing.·DistL- x x' y))
        (sym (ℝRing.·DistR- x' y y'))


rectangularProductChosenCauchyWithBounds :
  ∀ (A B : ℚ₊) (x y : RealSequence) →
  (∀ n → absℝ (x n) ≤ℝ rat (fst A)) →
  (∀ n → absℝ (y n) ≤ℝ rat (fst B)) →
  ChosenIsCauchySequence x →
  ChosenIsCauchySequence y →
  ChosenIsCauchySequence (λ n → x n · y n)
rectangularProductChosenCauchyWithBounds
  A B x y x-bounded y-bounded
  x-chosen y-chosen .fst ε =
  ℕ.max
    (fst x-chosen (x-radius ε))
    (fst y-chosen (y-radius ε))
  where
  x-radius : ℚ₊ → ℚ₊
  x-radius ε = (ε /4₊) ₊／₊ B

  y-radius : ℚ₊ → ℚ₊
  y-radius ε = (ε /4₊) ₊／₊ A
rectangularProductChosenCauchyWithBounds
  A B x y x-bounded y-bounded
  x-chosen y-chosen .snd
  ε m n max≤m max≤n =
  absDifference<→closeness
    (x m · y m) (x n · y n) ε
    (≤<ℝ-trans
      (absℝ (x m · y m - x n · y n))
      (rat (fst (ε /2₊)))
      (rat (fst ε))
      half-bound
      (<ℚ→<ℝ
        (fst (ε /2₊)) (fst ε) (/2₊<id ε)))
  where
  x-radius : ℚ₊ → ℚ₊
  x-radius ε = (ε /4₊) ₊／₊ B

  y-radius : ℚ₊ → ℚ₊
  y-radius ε = (ε /4₊) ₊／₊ A

  x-close : x m ∼[ x-radius ε ] x n
  x-close =
    snd x-chosen (x-radius ε) m n
      (ℕ.≤-trans
        (ℕ.left-≤-max
          {m = fst x-chosen (x-radius ε)}
          {n = fst y-chosen (y-radius ε)})
        max≤m)
      (ℕ.≤-trans
        (ℕ.left-≤-max
          {m = fst x-chosen (x-radius ε)}
          {n = fst y-chosen (y-radius ε)})
        max≤n)

  y-close : y m ∼[ y-radius ε ] y n
  y-close =
    snd y-chosen (y-radius ε) m n
      (ℕ.≤-trans
        (ℕ.right-≤-max
          {n = fst y-chosen (y-radius ε)}
          {m = fst x-chosen (x-radius ε)})
        max≤m)
      (ℕ.≤-trans
        (ℕ.right-≤-max
          {n = fst y-chosen (y-radius ε)}
          {m = fst x-chosen (x-radius ε)})
        max≤n)

  x-radius-nonnegative :
    0ℝ ≤ℝ rat (fst (x-radius ε))
  x-radius-nonnegative =
    ≤ℚ→≤ℝ 0 (fst (x-radius ε))
      (ℚ.<Weaken≤ 0 (fst (x-radius ε))
        (snd (x-radius ε)))

  y-radius-nonnegative :
    0ℝ ≤ℝ rat (fst (y-radius ε))
  y-radius-nonnegative =
    ≤ℚ→≤ℝ 0 (fst (y-radius ε))
      (ℚ.<Weaken≤ 0 (fst (y-radius ε))
        (snd (y-radius ε)))

  x-term-bound :
    absℝ ((x m - x n) · y m) ≤ℝ
    rat (fst (ε /4₊))
  x-term-bound =
    subst2 _≤ℝ_
      (sym (absMul (x m - x n) (y m)))
      ( mul-rat (fst (x-radius ε)) (fst B)
      ∙ cong rat
          ( ℚ.·Comm (fst (x-radius ε)) (fst B)
          ∙ ·／ B (ε /4₊)))
      (mulPres≤
        (absℝ (x m - x n))
        (rat (fst (x-radius ε)))
        (absℝ (y m))
        (rat (fst B))
        x-radius-nonnegative
        (absNonnegative (y m))
        (<ℝ-weaken
          (absℝ (x m - x n))
          (rat (fst (x-radius ε)))
          (closeness→absDifference<
            (x m) (x n) (x-radius ε) x-close))
        (y-bounded m))

  y-term-bound :
    absℝ (x n · (y m - y n)) ≤ℝ
    rat (fst (ε /4₊))
  y-term-bound =
    subst2 _≤ℝ_
      (sym (absMul (x n) (y m - y n)))
      ( mul-rat (fst A) (fst (y-radius ε))
      ∙ cong rat (·／ A (ε /4₊)))
      (mulPres≤
        (absℝ (x n))
        (rat (fst A))
        (absℝ (y m - y n))
        (rat (fst (y-radius ε)))
        (≤ℚ→≤ℝ 0 (fst A)
          (ℚ.<Weaken≤ 0 (fst A) (snd A)))
        (absNonnegative (y m - y n))
        (x-bounded n)
        (<ℝ-weaken
          (absℝ (y m - y n))
          (rat (fst (y-radius ε)))
          (closeness→absDifference<
            (y m) (y n) (y-radius ε) y-close)))

  half-bound :
    absℝ (x m · y m - x n · y n) ≤ℝ
    rat (fst (ε /2₊))
  half-bound =
    subst
      (_≤ℝ rat (fst (ε /2₊)))
      (sym
        (cong absℝ
          (productDifferencePath
            (x m) (x n) (y m) (y n))))
      (≤ℝ-trans
        (absℝ
          ((x m - x n) · y m +
            x n · (y m - y n)))
        (absℝ ((x m - x n) · y m) +
          absℝ (x n · (y m - y n)))
        (rat (fst (ε /2₊)))
        (absTriangle
          ((x m - x n) · y m)
          (x n · (y m - y n)))
        sum-bound)
    where
    sum-bound :
      absℝ ((x m - x n) · y m) +
          absℝ (x n · (y m - y n))
        ≤ℝ
      rat (fst (ε /2₊))
    sum-bound =
      subst
        ( (absℝ ((x m - x n) · y m) +
            absℝ (x n · (y m - y n))) ≤ℝ_)
        ( rat+rat (fst (ε /4₊)) (fst (ε /4₊))
        ∙ cong rat (/4+/4≡/2 (fst ε)))
        (addPres≤
          (absℝ ((x m - x n) · y m))
          (rat (fst (ε /4₊)))
          (absℝ (x n · (y m - y n)))
          (rat (fst (ε /4₊)))
          x-term-bound y-term-bound)


chosenMertensRemainderCauchyWithBounds :
  ∀ (A B : ℚ₊) (a b : RealSequence) →
  UniformAbsolutePartialSumBound A a →
  UniformPartialSumAbsBound B b →
  ChosenIsCauchySequence (partialSum (absℝ ∘ a)) →
  ChosenIsCauchySequence (partialSum b) →
  ChosenIsCauchySequence (cauchyProductRemainder a b)
chosenMertensRemainderCauchyWithBounds
  A B a b a-bounded b-bounded
  a-chosen b-chosen .fst ε =
  mertensModulus
    A B a b a-bounded b-bounded a-chosen b-chosen
    (ε /4₊)
chosenMertensRemainderCauchyWithBounds
  A B a b a-bounded b-bounded
  a-chosen b-chosen .snd
  ε m n modulus≤m modulus≤n =
  Pℝ.isMonotone≈<
    (cauchyProductRemainder a b m)
    (cauchyProductRemainder a b n)
    (ε /2₊) ε (/2₊<id ε)
    (Pℝ.subst≈
      (cauchyProductRemainder a b m)
      (cauchyProductRemainder a b n)
      (/4+/4≡/2 (fst ε))
      (triangle∼
        (cauchyProductRemainder a b m)
        0ℝ
        (cauchyProductRemainder a b n)
        (ε /4₊) (ε /4₊)
        (remainder-close-zero m modulus≤m)
        (sym∼
          (cauchyProductRemainder a b n) 0ℝ
          (ε /4₊)
          (remainder-close-zero n modulus≤n))))
  where
  remainder-close-zero : ∀ n →
    mertensModulus
      A B a b a-bounded b-bounded a-chosen b-chosen
      (ε /4₊)
      ℕ.≤ n →
    cauchyProductRemainder a b n ∼[ ε /4₊ ] 0ℝ
  remainder-close-zero n modulus≤n =
    absDifference<→closeness
      (cauchyProductRemainder a b n) 0ℝ (ε /4₊)
      (subst
        (_<ℝ rat (fst (ε /4₊)))
        (sym
          (cong absℝ
            (subZero (cauchyProductRemainder a b n))))
        (≤<ℝ-trans
          (absℝ (cauchyProductRemainder a b n))
          (partialSum
            (cauchyProductRemainderMajorant a b n) n)
          (rat (fst (ε /4₊)))
          (cauchyProductRemainderAbsBound a b n)
          (fullMajorantBound
            A B a b a-bounded b-bounded a-chosen b-chosen
            (ε /4₊) n modulus≤n)))


differenceChosenCauchy : ∀ (x y : RealSequence) →
  ChosenIsCauchySequence x →
  ChosenIsCauchySequence y →
  ChosenIsCauchySequence (λ n → x n - y n)
differenceChosenCauchy x y x-chosen y-chosen .fst ε =
  ℕ.max
    (fst x-chosen (ε /2₊))
    (fst y-chosen (ε /2₊))
differenceChosenCauchy x y x-chosen y-chosen .snd
  ε m n max≤m max≤n =
  Pℝ.subst≈
    (x m - y m) (x n - y n)
    (/2+/2≡id (fst ε))
    (add-pres∼
      (x m) (x n) (- y m) (- y n)
      (ε /2₊) (ε /2₊)
      (snd x-chosen (ε /2₊) m n
        (ℕ.≤-trans
          (ℕ.left-≤-max
            {m = fst x-chosen (ε /2₊)}
            {n = fst y-chosen (ε /2₊)})
          max≤m)
        (ℕ.≤-trans
          (ℕ.left-≤-max
            {m = fst x-chosen (ε /2₊)}
            {n = fst y-chosen (ε /2₊)})
          max≤n))
      (neg-isNonExpanding .IsNonExpanding.pres≈
        (y m) (y n) (ε /2₊)
        (snd y-chosen (ε /2₊) m n
          (ℕ.≤-trans
            (ℕ.right-≤-max
              {n = fst y-chosen (ε /2₊)}
              {m = fst x-chosen (ε /2₊)})
            max≤m)
          (ℕ.≤-trans
            (ℕ.right-≤-max
              {n = fst y-chosen (ε /2₊)}
              {m = fst x-chosen (ε /2₊)})
            max≤n))))


chosenMertensCauchyProductWithBounds :
  ∀ (A B : ℚ₊) (a b : RealSequence) →
  UniformAbsolutePartialSumBound A a →
  UniformPartialSumAbsBound B b →
  ChosenIsCauchySequence (partialSum (absℝ ∘ a)) →
  ChosenIsCauchySequence (partialSum b) →
  ChosenIsCauchySequence (partialSum (cauchyProduct a b))
chosenMertensCauchyProductWithBounds
  A B a b a-bounded b-bounded
  a-absolute-chosen b-chosen =
  subst
    ChosenIsCauchySequence
    (sym
      (funExt
        (partialSum-cauchyProduct-as-rectangle-minus-remainder
          a b)))
    (differenceChosenCauchy
      rectangular-product
      (cauchyProductRemainder a b)
      rectangular-product-chosen
      remainder-chosen)
  where
  rectangular-product : RealSequence
  rectangular-product n =
    partialSum a n · partialSum b n

  a-chosen :
    ChosenIsCauchySequence (partialSum a)
  a-chosen =
    dominatedChosenCauchySeriesIsChosenCauchy
      a (absℝ ∘ a)
      (λ n → ≤ℝ-refl (absℝ (a n)))
      a-absolute-chosen

  rectangular-product-chosen :
    ChosenIsCauchySequence rectangular-product
  rectangular-product-chosen =
    rectangularProductChosenCauchyWithBounds
      A B (partialSum a) (partialSum b)
      (uniformAbsoluteBound→uniformBound A a a-bounded)
      b-bounded
      a-chosen b-chosen

  remainder-chosen :
    ChosenIsCauchySequence (cauchyProductRemainder a b)
  remainder-chosen =
    chosenMertensRemainderCauchyWithBounds
      A B a b a-bounded b-bounded
      a-absolute-chosen b-chosen


chosenCauchyProductIsAbsolutelyCauchyWithBounds :
  ∀ (A B : ℚ₊) (a b : RealSequence) →
  UniformAbsolutePartialSumBound A a →
  UniformAbsolutePartialSumBound B b →
  ChosenIsCauchySequence (partialSum (absℝ ∘ a)) →
  ChosenIsCauchySequence (partialSum (absℝ ∘ b)) →
  ChosenIsCauchySequence
    (partialSum (absℝ ∘ cauchyProduct a b))
chosenCauchyProductIsAbsolutelyCauchyWithBounds
  A B a b a-bounded b-bounded
  a-absolute-chosen b-absolute-chosen =
  dominatedChosenCauchySeriesIsChosenCauchy
    (absℝ ∘ cauchyProduct a b)
    (absoluteCauchyProduct a b)
    dominates
    absolute-product-chosen
  where
  absolute-product-chosen :
    ChosenIsCauchySequence
      (partialSum (absoluteCauchyProduct a b))
  absolute-product-chosen =
    chosenMertensCauchyProductWithBounds
      A B
      (absℝ ∘ a) (absℝ ∘ b)
      (absoluteSequencePresUniformAbsoluteBound A a a-bounded)
      (absolutePartialSumBound→absoluteSequenceBound
        B b b-bounded)
      (absoluteSequenceChosenIsAbsolutelyCauchy
        a a-absolute-chosen)
      b-absolute-chosen

  dominates : ∀ n →
    absℝ (absℝ (cauchyProduct a b n)) ≤ℝ
    absoluteCauchyProduct a b n
  dominates n =
    subst
      (_≤ℝ absoluteCauchyProduct a b n)
      (sym (absIdem (cauchyProduct a b n)))
      (cauchyProductAbsBound a b n)


nativeCauchyProductIsAbsolutelyCauchy : ∀ a b →
  IsAbsolutelyCauchySeries a →
  IsAbsolutelyCauchySeries b →
  IsAbsolutelyCauchySeries (cauchyProduct a b)
nativeCauchyProductIsAbsolutelyCauchy
  a b a-absolute b-absolute =
  PT.rec
    (isPropIsAbsolutelyCauchySeries (cauchyProduct a b))
    (λ a-chosen →
      PT.rec
        (isPropIsAbsolutelyCauchySeries (cauchyProduct a b))
        (λ b-chosen →
          PT.rec
            (isPropIsAbsolutelyCauchySeries (cauchyProduct a b))
            (λ where
              (A , a-bounded) →
                PT.rec
                  (isPropIsAbsolutelyCauchySeries
                    (cauchyProduct a b))
                  (λ where
                    (B , b-bounded) →
                      ∣ chosenCauchyProductIsAbsolutelyCauchyWithBounds
                          A B a b a-bounded b-bounded
                          a-chosen b-chosen
                      ∣₁)
                  (mereAbsolutelyCauchySeriesUniformAbsolutePartialSumBound
                    b b-absolute))
            (mereAbsolutelyCauchySeriesUniformAbsolutePartialSumBound
              a a-absolute))
        b-absolute)
    a-absolute


-- Downstream iterative constructions should normally use the sealed entry
-- point so that the quantitative modulus proof is not normalized again.

opaque
  nativeCauchyProductIsAbsolutelyCauchy-sealed : ∀ a b →
    IsAbsolutelyCauchySeries a →
    IsAbsolutelyCauchySeries b →
    IsAbsolutelyCauchySeries (cauchyProduct a b)
  nativeCauchyProductIsAbsolutelyCauchy-sealed =
    nativeCauchyProductIsAbsolutelyCauchy
