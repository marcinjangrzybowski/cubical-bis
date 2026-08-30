module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Convolution where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat as ℕ
  using (ℕ ; zero ; suc ; _∸_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Continuity
  using (add-pres≈₁ ; add-pres≈₂)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (abs-mul)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (closeness→absDifference< ; absDifference<→closeness)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.FiniteSum
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Absolute


-- Finite convolution -----------------------------------------------------

partialSum-first : ∀ terms n →
  partialSum terms (suc n) ≡
  terms zero Add.+ partialSum (terms ∘ suc) n
partialSum-first terms zero =
  add-zero-left (terms zero)
  ∙ sym (add-zero-right (terms zero))
partialSum-first terms (suc n) =
  cong (Add._+ terms (suc n))
    (partialSum-first terms n)
  ∙ sym
      (add-assoc
        (terms zero)
        (partialSum (terms ∘ suc) n)
        (terms (suc n)))


boundedSubtractInvolutive :
  ∀ k n → k ℕ.≤ n → k ≡ n ∸ (n ∸ k)
boundedSubtractInvolutive k n k≤n =
  ℕ.inj-+m
    ( ℕ.+-comm k (n ∸ k)
    ∙ ℕ.[n-m]+m k n k≤n
    ∙ sym
        (ℕ.[n-m]+m
          (n ∸ k) n
          (ℕ.∸-≤ n k))
    )


partialSum-reverse : ∀ terms n →
  partialSum terms (suc n) ≡
  partialSum (λ k → terms (n ∸ k)) (suc n)
partialSum-reverse terms zero = refl
partialSum-reverse terms (suc n) =
  cong (Add._+ terms (suc n))
    (partialSum-reverse terms n)
  ∙ add-comm
      (partialSum (λ k → terms (n ∸ k)) (suc n))
      (terms (suc n))
  ∙ sym
      (partialSum-first
        (λ k → terms (suc n ∸ k))
        (suc n))


partialSum-right-scale : ∀ terms c n →
  partialSum (λ k → terms k Mul.· c) n ≡
  partialSum terms n Mul.· c
partialSum-right-scale terms c zero =
  sym (mul-zero-left c)
partialSum-right-scale terms c (suc n) =
  cong (Add._+ (terms n Mul.· c))
    (partialSum-right-scale terms c n)
  ∙ sym
      (mul-distrib-over-add-left
        (partialSum terms n) (terms n) c)


rectangularSum :
  RealSequence → RealSequence → ℕ → ℕ → Real.ℝ
rectangularSum a b m n =
  partialSum (λ i → a i Mul.· partialSum b n) m


rectangularSum-product : ∀ a b m n →
  rectangularSum a b m n ≡
  partialSum a m Mul.· partialSum b n
rectangularSum-product a b m n =
  partialSum-right-scale a (partialSum b n) m


cauchyProduct :
  RealSequence → RealSequence → RealSequence
cauchyProduct a b n =
  partialSum (λ k → a k Mul.· b (n ∸ k)) (suc n)


cauchyProduct-zero : ∀ a b →
  cauchyProduct a b zero ≡ a zero Mul.· b zero
cauchyProduct-zero a b =
  add-zero-left (a zero Mul.· b zero)


cauchyProduct-comm : ∀ a b n →
  cauchyProduct a b n ≡ cauchyProduct b a n
cauchyProduct-comm a b n =
  partialSum-reverse
    (λ k → a k Mul.· b (n ∸ k)) n
  ∙ partialSum-pointwiseBefore
      (λ k → a (n ∸ k) Mul.· b (n ∸ (n ∸ k)))
      (λ k → b k Mul.· a (n ∸ k))
      (suc n)
      summand-path
  where
  summand-path : ∀ k → k ℕ.< suc n →
    a (n ∸ k) Mul.· b (n ∸ (n ∸ k)) ≡
    b k Mul.· a (n ∸ k)
  summand-path k k<sucn =
    cong (a (n ∸ k) Mul.·_)
      (cong b
        (sym
          (boundedSubtractInvolutive
            k n (ℕ.pred-≤-pred k<sucn))))
    ∙ mul-comm (a (n ∸ k)) (b k)


cauchyProduct-comm-sequence : ∀ a b →
  cauchyProduct a b ≡ cauchyProduct b a
cauchyProduct-comm-sequence a b =
  funExt (cauchyProduct-comm a b)


cauchyProduct-left-step : ∀ a b n →
  cauchyProduct a b (suc n) ≡
  a zero Mul.· b (suc n)
    Add.+ cauchyProduct (a ∘ suc) b n
cauchyProduct-left-step a b n =
  partialSum-first
    (λ k → a k Mul.· b (suc n ∸ k))
    (suc n)


singletonSeries : Real.ℝ → RealSequence
singletonSeries c zero = c
singletonSeries c (suc _) = zeroℝ


partialSum-singletonSeries : ∀ c n →
  partialSum (singletonSeries c) (suc n) ≡ c
partialSum-singletonSeries c zero =
  add-zero-left c
partialSum-singletonSeries c (suc n) =
  cong (Add._+ zeroℝ)
    (partialSum-singletonSeries c n)
  ∙ add-zero-right c


cauchyProduct-zeroLeft : ∀ b n →
  cauchyProduct (λ _ → zeroℝ) b n ≡ zeroℝ
cauchyProduct-zeroLeft b n =
  partialSum-pointwise
    (λ k → zeroℝ Mul.· b (n ∸ k))
    (λ _ → zeroℝ)
    (λ k → mul-zero-left (b (n ∸ k)))
    (suc n)
  ∙ partialSum-zeroSequence (suc n)


cauchyProduct-singleton-left : ∀ c b n →
  cauchyProduct (singletonSeries c) b n ≡
  scaleSeries c b n
cauchyProduct-singleton-left c b zero =
  cauchyProduct-zero (singletonSeries c) b
cauchyProduct-singleton-left c b (suc n) =
  cauchyProduct-left-step (singletonSeries c) b n
  ∙ cong (c Mul.· b (suc n) Add.+_)
      (cauchyProduct-zeroLeft b n)
  ∙ add-zero-right (c Mul.· b (suc n))


triangularRows :
  RealSequence → RealSequence → ℕ → Real.ℝ
triangularRows a b n =
  partialSum
    (λ i → a i Mul.· partialSum b (n ∸ i)) n


triangularRows-step : ∀ a b n →
  triangularRows a b (suc n) ≡
  triangularRows a b n Add.+ cauchyProduct a b n
triangularRows-step a b zero =
  cong (λ x → zeroℝ Add.+ a zero Mul.· x)
      (add-zero-left (b zero))
  ∙ add-zero-left (a zero Mul.· b zero)
  ∙ sym (add-zero-left (a zero Mul.· b zero))
  ∙ cong (zeroℝ Add.+_)
      (sym (cauchyProduct-zero a b))
triangularRows-step a b (suc n) =
  partialSum-first
    (λ i → a i Mul.· partialSum b (suc (suc n) ∸ i))
    (suc n)
  ∙ cong
      (a zero Mul.· partialSum b (suc (suc n)) Add.+_)
      (triangularRows-step (a ∘ suc) b n)
  ∙ cong
      (Add._+
        (triangularRows (a ∘ suc) b n
          Add.+ cauchyProduct (a ∘ suc) b n))
      (mul-distrib-over-add-right
        (a zero) (partialSum b (suc n)) (b (suc n)))
  ∙ interchange
  ∙ cong₂ Add._+_
      (sym
        (partialSum-first
          (λ i → a i Mul.· partialSum b (suc n ∸ i)) n))
      (sym (cauchyProduct-left-step a b n))
  where
  interchange :
    a zero Mul.· partialSum b (suc n)
      Add.+ a zero Mul.· b (suc n)
      Add.+ (triangularRows (a ∘ suc) b n
        Add.+ cauchyProduct (a ∘ suc) b n) ≡
    (a zero Mul.· partialSum b (suc n)
      Add.+ triangularRows (a ∘ suc) b n)
      Add.+
    (a zero Mul.· b (suc n)
      Add.+ cauchyProduct (a ∘ suc) b n)
  interchange =
    sym
      (add-assoc
        (a zero Mul.· partialSum b (suc n))
        (a zero Mul.· b (suc n))
        (triangularRows (a ∘ suc) b n
          Add.+ cauchyProduct (a ∘ suc) b n))
    ∙ cong (a zero Mul.· partialSum b (suc n) Add.+_)
        ( add-assoc
            (a zero Mul.· b (suc n))
            (triangularRows (a ∘ suc) b n)
            (cauchyProduct (a ∘ suc) b n)
        ∙ cong (Add._+ cauchyProduct (a ∘ suc) b n)
            (add-comm
              (a zero Mul.· b (suc n))
              (triangularRows (a ∘ suc) b n))
        ∙ sym
            (add-assoc
              (triangularRows (a ∘ suc) b n)
              (a zero Mul.· b (suc n))
              (cauchyProduct (a ∘ suc) b n))
        )
    ∙ add-assoc
        (a zero Mul.· partialSum b (suc n))
        (triangularRows (a ∘ suc) b n)
        (a zero Mul.· b (suc n)
          Add.+ cauchyProduct (a ∘ suc) b n)


partialSum-cauchyProduct : ∀ a b n →
  partialSum (cauchyProduct a b) n ≡
  triangularRows a b n
partialSum-cauchyProduct a b zero = refl
partialSum-cauchyProduct a b (suc n) =
  cong (Add._+ cauchyProduct a b n)
    (partialSum-cauchyProduct a b n)
  ∙ sym (triangularRows-step a b n)


-- Absolute majorants ----------------------------------------------------

absoluteCauchyProduct :
  RealSequence → RealSequence → RealSequence
absoluteCauchyProduct a b =
  cauchyProduct (Abs.absℝ ∘ a) (Abs.absℝ ∘ b)


cauchyProductAbsBound : ∀ a b n →
  Abs.absℝ (cauchyProduct a b n) ≤ℝ
  absoluteCauchyProduct a b n
cauchyProductAbsBound a b n =
  subst
    (Abs.absℝ (cauchyProduct a b n) ≤ℝ_)
    absoluteSummands≡positiveSummands
    (partialSumAbsBound
      (λ k → a k Mul.· b (n ∸ k)) (suc n))
  where
  absoluteSummands≡positiveSummands :
    partialSum
      (Abs.absℝ ∘ (λ k → a k Mul.· b (n ∸ k)))
      (suc n) ≡
    absoluteCauchyProduct a b n
  absoluteSummands≡positiveSummands =
    partialSum-pointwise
      (Abs.absℝ ∘ (λ k → a k Mul.· b (n ∸ k)))
      (λ k → Abs.absℝ (a k) Mul.· Abs.absℝ (b (n ∸ k)))
      (λ k → abs-mul (a k) (b (n ∸ k)))
      (suc n)


absoluteCauchyProductFromMajorant : ∀ a b →
  IsCauchySeries (absoluteCauchyProduct a b) →
  IsAbsolutelyCauchySeries (cauchyProduct a b)
absoluteCauchyProductFromMajorant a b positive-product-cauchy =
  dominatedCauchySeriesIsCauchy
    (Abs.absℝ ∘ cauchyProduct a b)
    (absoluteCauchyProduct a b)
    dominates positive-product-cauchy
  where
  dominates : ∀ n →
    Abs.absℝ (Abs.absℝ (cauchyProduct a b n)) ≤ℝ
    absoluteCauchyProduct a b n
  dominates n =
    subst
      (_≤ℝ absoluteCauchyProduct a b n)
      (sym (Abs.absℝ-idempotent (cauchyProduct a b n)))
      (cauchyProductAbsBound a b n)


-- Rectangular approximation --------------------------------------------

CauchyProductRectangularApproximation :
  RealSequence → RealSequence → Type₀
CauchyProductRectangularApproximation a b =
  EventuallyClose
    (λ n → partialSum a n Mul.· partialSum b n)
    (partialSum (cauchyProduct a b))


singletonRectangularPartialSums : ∀ c b n →
  partialSum (singletonSeries c) n Mul.· partialSum b n ≡
  partialSum (cauchyProduct (singletonSeries c) b) n
singletonRectangularPartialSums c b zero =
  mul-zero-left zeroℝ
singletonRectangularPartialSums c b (suc n) =
  cong (Mul._· partialSum b (suc n))
      (partialSum-singletonSeries c n)
  ∙ sym (partialSum-scale c b (suc n))
  ∙ sym
      (partialSum-pointwise
        (cauchyProduct (singletonSeries c) b)
        (scaleSeries c b)
        (cauchyProduct-singleton-left c b)
        (suc n))


singletonRectangularApproximation : ∀ c b →
  CauchyProductRectangularApproximation
    (singletonSeries c) b
singletonRectangularApproximation c b ε =
  ∣ 0 , (λ n _ →
      subst
        (λ z → z Real.Base.≈ᶜ[ ε ]
          partialSum (cauchyProduct (singletonSeries c) b) n)
        (sym (singletonRectangularPartialSums c b n))
        (Real.Base.isRefl≈ᶜ
          (partialSum (cauchyProduct (singletonSeries c) b) n)
          ε)) ∣₁


cauchyProductRemainder :
  RealSequence → RealSequence → RealSequence
cauchyProductRemainder a b n =
  partialSum
    (λ i →
      a i Mul.·
        (partialSum b n Group.- partialSum b (n ∸ i)))
    n


cauchyProductRemainderMajorant :
  RealSequence → RealSequence → ℕ → RealSequence
cauchyProductRemainderMajorant a b n i =
  Abs.absℝ (a i) Mul.·
    Abs.absℝ
      (partialSum b n Group.- partialSum b (n ∸ i))


cauchyProductRemainderAbsBound : ∀ a b n →
  Abs.absℝ (cauchyProductRemainder a b n) ≤ℝ
  partialSum (cauchyProductRemainderMajorant a b n) n
cauchyProductRemainderAbsBound a b n =
  subst
    (Abs.absℝ (cauchyProductRemainder a b n) ≤ℝ_)
    absoluteSummands≡majorant
    (partialSumAbsBound
      (λ i → a i Mul.·
        (partialSum b n Group.- partialSum b (n ∸ i)))
      n)
  where
  absoluteSummands≡majorant :
    partialSum
      (Abs.absℝ ∘
        (λ i → a i Mul.·
          (partialSum b n Group.- partialSum b (n ∸ i))))
      n ≡
    partialSum (cauchyProductRemainderMajorant a b n) n
  absoluteSummands≡majorant =
    partialSum-pointwise
      (Abs.absℝ ∘
        (λ i → a i Mul.·
          (partialSum b n Group.- partialSum b (n ∸ i))))
      (cauchyProductRemainderMajorant a b n)
      (λ i → abs-mul
        (a i)
        (partialSum b n Group.- partialSum b (n ∸ i)))
      n


triangularRows-plus-remainder : ∀ a b n →
  triangularRows a b n Add.+ cauchyProductRemainder a b n ≡
  rectangularSum a b n n
triangularRows-plus-remainder a b n =
  sym
    (partialSum-add
      (λ i → a i Mul.· partialSum b (n ∸ i))
      (λ i → a i Mul.·
        (partialSum b n Group.- partialSum b (n ∸ i)))
      n)
  ∙ partialSum-pointwise
      (λ i →
        a i Mul.· partialSum b (n ∸ i) Add.+
        a i Mul.·
          (partialSum b n Group.- partialSum b (n ∸ i)))
      (λ i → a i Mul.· partialSum b n)
      summand-path n
  where
  summand-path : ∀ i →
    a i Mul.· partialSum b (n ∸ i) Add.+
    a i Mul.·
      (partialSum b n Group.- partialSum b (n ∸ i)) ≡
    a i Mul.· partialSum b n
  summand-path i =
    sym
      (mul-distrib-over-add-right
        (a i)
        (partialSum b (n ∸ i))
        (partialSum b n Group.- partialSum b (n ∸ i)))
    ∙ cong (a i Mul.·_)
        ( add-comm
            (partialSum b (n ∸ i))
            (partialSum b n Group.- partialSum b (n ∸ i))
        ∙ sub-add-cancel
            (partialSum b n) (partialSum b (n ∸ i))
        )


rectangularProduct-decomposition : ∀ a b n →
  partialSum a n Mul.· partialSum b n ≡
  partialSum (cauchyProduct a b) n Add.+
    cauchyProductRemainder a b n
rectangularProduct-decomposition a b n =
  sym (rectangularSum-product a b n n)
  ∙ sym (triangularRows-plus-remainder a b n)
  ∙ cong (Add._+ cauchyProductRemainder a b n)
      (sym (partialSum-cauchyProduct a b n))


-- The remainder condition is intentionally radiuswise: every requested
-- error gets a merely existing cutoff.  It is not strengthened to a single
-- chosen modulus, since that would reintroduce the tail-choice principle.

CauchyProductRemainderVanishes :
  RealSequence → RealSequence → Type₀
CauchyProductRemainderVanishes a b =
  EventuallyClose (cauchyProductRemainder a b) (λ _ → zeroℝ)


ChosenCauchyProductRemainderVanishes :
  RealSequence → RealSequence → Type₀
ChosenCauchyProductRemainderVanishes a b =
  Σ[ modulus ∈ (ℚ₊ → ℕ) ]
    (∀ ε n → modulus ε ℕ.≤ n →
      cauchyProductRemainder a b n
        Real.Base.≈ᶜ[ ε ] zeroℝ)


chosenRemainderVanishes→remainderVanishes : ∀ a b →
  ChosenCauchyProductRemainderVanishes a b →
  CauchyProductRemainderVanishes a b
chosenRemainderVanishes→remainderVanishes
  a b (modulus , close) ε =
  ∣ modulus ε , close ε ∣₁


remainderVanishes→rectangularApproximation : ∀ a b →
  CauchyProductRemainderVanishes a b →
  CauchyProductRectangularApproximation a b
remainderVanishes→rectangularApproximation
  a b remainder-vanishes ε =
  PT.map
    (λ { (N , close) →
      N , λ n N≤n →
        subst2 (Real.Base._≈ᶜ[ ε ]_)
          (sym (rectangularProduct-decomposition a b n))
          (add-zero-right (partialSum (cauchyProduct a b) n))
          (add-pres≈₂
            (partialSum (cauchyProduct a b) n)
            (cauchyProductRemainder a b n) zeroℝ ε
            (close n N≤n)) })
    (remainder-vanishes ε)


rectangularApproximation→remainderVanishes : ∀ a b →
  CauchyProductRectangularApproximation a b →
  CauchyProductRemainderVanishes a b
rectangularApproximation→remainderVanishes
  a b approximation ε =
  PT.map
    (λ { (N , close) →
      N , λ n N≤n →
        subst2 (Real.Base._≈ᶜ[ ε ]_)
          (remainder-path n)
          (sub-self (partialSum (cauchyProduct a b) n))
          (add-pres≈₁
            (partialSum a n Mul.· partialSum b n)
            (partialSum (cauchyProduct a b) n)
            (Neg.- partialSum (cauchyProduct a b) n)
            ε (close n N≤n)) })
    (approximation ε)
  where
  remainder-path : ∀ n →
    partialSum a n Mul.· partialSum b n
      Group.- partialSum (cauchyProduct a b) n ≡
    cauchyProductRemainder a b n
  remainder-path n =
    cong
      (Group._- partialSum (cauchyProduct a b) n)
      (rectangularProduct-decomposition a b n)
    ∙ cong
        (Group._- partialSum (cauchyProduct a b) n)
        (add-comm
          (partialSum (cauchyProduct a b) n)
          (cauchyProductRemainder a b n))
    ∙ add-sub-cancel
        (cauchyProductRemainder a b n)
        (partialSum (cauchyProduct a b) n)


remainderVanishes≃rectangularApproximation : ∀ a b →
  CauchyProductRemainderVanishes a b ≃
  CauchyProductRectangularApproximation a b
remainderVanishes≃rectangularApproximation a b =
  propBiimpl→Equiv
    (isPropEventuallyClose
      (cauchyProductRemainder a b) (λ _ → zeroℝ))
    (isPropEventuallyClose
      (λ n → partialSum a n Mul.· partialSum b n)
      (partialSum (cauchyProduct a b)))
    (remainderVanishes→rectangularApproximation a b)
    (rectangularApproximation→remainderVanishes a b)


-- Cauchy products and sums ---------------------------------------------
--
-- No uniform bound is needed here.  The two partial-sum sequences are
-- natively Cauchy, and multiplication already preserves native Cauchy
-- sequences.  This removes the common rational bound premise from the
-- corresponding chosen-modulus development.

cauchyProductIsCauchy : ∀ a b →
  IsCauchySeries a → IsCauchySeries b →
  CauchyProductRectangularApproximation a b →
  IsCauchySeries (cauchyProduct a b)
cauchyProductIsCauchy a b a-cauchy b-cauchy approximation =
  eventuallyClosePresIsCauchySequence approximation
    (mulPresIsCauchySequence a-cauchy b-cauchy)


cauchyProductIsCauchyWithRemainder : ∀ a b →
  IsCauchySeries a → IsCauchySeries b →
  CauchyProductRemainderVanishes a b →
  IsCauchySeries (cauchyProduct a b)
cauchyProductIsCauchyWithRemainder
  a b a-cauchy b-cauchy remainder-vanishes =
  cauchyProductIsCauchy a b a-cauchy b-cauchy
    (remainderVanishes→rectangularApproximation
      a b remainder-vanishes)


cauchyProductHasSum : ∀ a b a-sum b-sum →
  HasSum a a-sum → HasSum b b-sum →
  CauchyProductRectangularApproximation a b →
  HasSum (cauchyProduct a b) (a-sum Mul.· b-sum)
cauchyProductHasSum
  a b a-sum b-sum a-has-sum b-has-sum approximation =
  eventuallyClosePresIsLimitSequence approximation
    (mulPresIsLimitSequence a-has-sum b-has-sum)


cauchyProductHasSumWithRemainder : ∀ a b a-sum b-sum →
  HasSum a a-sum → HasSum b b-sum →
  CauchyProductRemainderVanishes a b →
  HasSum (cauchyProduct a b) (a-sum Mul.· b-sum)
cauchyProductHasSumWithRemainder
  a b a-sum b-sum a-has-sum b-has-sum remainder-vanishes =
  cauchyProductHasSum a b a-sum b-sum
    a-has-sum b-has-sum
    (remainderVanishes→rectangularApproximation
      a b remainder-vanishes)


cauchyProductSummable : ∀ a b →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  CauchyProductRectangularApproximation a b →
  Summable (cauchyProduct a b)
cauchyProductSummable
  a b a-summable b-summable approximation =
  seriesSum a a-summable Mul.· seriesSum b b-summable
  , cauchyProductHasSum
      a b
      (seriesSum a a-summable)
      (seriesSum b b-summable)
      (seriesSumHasSum a a-summable)
      (seriesSumHasSum b b-summable)
      approximation


cauchyProductSummableWithRemainder : ∀ a b →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  CauchyProductRemainderVanishes a b →
  Summable (cauchyProduct a b)
cauchyProductSummableWithRemainder
  a b a-summable b-summable remainder-vanishes =
  cauchyProductSummable a b a-summable b-summable
    (remainderVanishes→rectangularApproximation
      a b remainder-vanishes)


seriesSum-cauchyProduct : ∀ a b
  (a-summable : Summable a)
  (b-summable : Summable b)
  (product-summable : Summable (cauchyProduct a b)) →
  CauchyProductRectangularApproximation a b →
  seriesSum (cauchyProduct a b) product-summable ≡
  seriesSum a a-summable Mul.· seriesSum b b-summable
seriesSum-cauchyProduct
  a b a-summable b-summable product-summable approximation =
  seriesSumIndependent
    (cauchyProduct a b) product-summable
    (cauchyProductSummable
      a b a-summable b-summable approximation)
