module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.DividedPowers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Nat as ℕ
  using (ℕ; zero; suc; _!; _∸_)
  renaming
    ( _choose_ to _chooseℕ_
    ; _+_ to _+ℕ_
    ; _·_ to _·ℕ_
    )
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base as ℚ using (ℚ; fromNat)
import Cubical.Data.Rationals.Properties as ℚP
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚAbs
open import Cubical.Data.Rationals.Inverse as ℚInv

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Data.FinData
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.Ring.BigOps

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.FiniteSum.Reindexing
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients


private
  module ℝBinomial = BinomialThm ℝCommRing
  module ℝSum = Sum (CommRing→Ring ℝCommRing)


-- Natural-number factorial and binomial identities --------------------

choose-above-offset : ∀ n offset →
  _chooseℕ_ n (suc (offset ℕ.+ n)) ≡ zero
choose-above-offset zero offset = refl
choose-above-offset (suc n) offset =
  cong (_chooseℕ_ (suc n) ∘ suc) (ℕ.+-suc offset n)
  ∙ cong₂ ℕ._+_
      (choose-above-offset n (suc offset))
      (choose-above-offset n offset)


choose-diagonal : ∀ n →
  _chooseℕ_ n n ≡ suc zero
choose-diagonal zero = refl
choose-diagonal (suc n) =
  cong₂ ℕ._+_
    (choose-above-offset n zero)
    (choose-diagonal n)


private
  move-left-factor : ∀ a b c →
    a ℕ.· (b ℕ.· c) ≡ b ℕ.· (a ℕ.· c)
  move-left-factor a b c =
    ℕ.·-assoc a b c
    ∙ cong (ℕ._· c) (ℕ.·-comm a b)
    ∙ sym (ℕ.·-assoc b a c)


-- This is the only polynomial rearrangement needed by the factorial
-- induction.  It is deliberately proved from the ordinary Nat laws rather
-- than by an arithmetic solver.
split-factorial-products : ∀ left right index index-factorial
  remainder remainder-factorial →
  (((left ℕ.+ right) ℕ.· (suc index ℕ.· index-factorial))
      ℕ.· (suc remainder ℕ.· remainder-factorial))
    ≡
  (suc remainder ℕ.·
      ((left ℕ.· (suc index ℕ.· index-factorial))
        ℕ.· remainder-factorial))
    ℕ.+
  (suc index ℕ.·
      ((right ℕ.· index-factorial)
        ℕ.· (suc remainder ℕ.· remainder-factorial)))
split-factorial-products left right index index-factorial
    remainder remainder-factorial =
  cong (ℕ._· (suc remainder ℕ.· remainder-factorial))
    (sym (ℕ.·-distribʳ left right
      (suc index ℕ.· index-factorial)))
  ∙ sym (ℕ.·-distribʳ
      (left ℕ.· (suc index ℕ.· index-factorial))
      (right ℕ.· (suc index ℕ.· index-factorial))
      (suc remainder ℕ.· remainder-factorial))
  ∙ cong₂ ℕ._+_ left-path right-path
  where
  left-product : ℕ
  left-product = left ℕ.· (suc index ℕ.· index-factorial)

  left-path :
    left-product ℕ.· (suc remainder ℕ.· remainder-factorial)
      ≡
    suc remainder ℕ.· (left-product ℕ.· remainder-factorial)
  left-path = move-left-factor left-product (suc remainder) remainder-factorial

  right-path :
    (right ℕ.· (suc index ℕ.· index-factorial)) ℕ.·
        (suc remainder ℕ.· remainder-factorial)
      ≡
    suc index ℕ.·
      ((right ℕ.· index-factorial) ℕ.·
        (suc remainder ℕ.· remainder-factorial))
  right-path =
    cong (ℕ._· (suc remainder ℕ.· remainder-factorial))
      (move-left-factor right (suc index) index-factorial)
    ∙ sym (ℕ.·-assoc
        (suc index)
        (right ℕ.· index-factorial)
        (suc remainder ℕ.· remainder-factorial))


choose-factorial-product : ∀ n k →
  k ℕ.≤ n →
  ((_chooseℕ_ n k ℕ.· (k !)) ℕ.· ((n ∸ k) !)) ≡ n !
choose-factorial-product zero zero k≤n = refl
choose-factorial-product zero (suc k) k≤n =
  ⊥.rec (ℕ.¬-<-zero k≤n)
choose-factorial-product (suc n) zero k≤n =
  ℕ.·-identityˡ ((suc n) !)
choose-factorial-product (suc n) (suc k) k+1≤n+1
  with ℕ.≤-split (ℕ.pred-≤-pred k+1≤n+1)
... | inr k≡n =
  subst
    (λ index →
      ((_chooseℕ_ (suc n) (suc index) ℕ.· ((suc index) !))
        ℕ.· ((suc n ∸ suc index) !))
      ≡ (suc n) !)
    (sym k≡n)
    diagonal
  where
  diagonal :
    ((_chooseℕ_ (suc n) (suc n) ℕ.· ((suc n) !))
      ℕ.· ((suc n ∸ suc n) !))
    ≡ (suc n) !
  diagonal =
    cong
      (λ coefficient →
        (coefficient ℕ.· ((suc n) !))
          ℕ.· ((suc n ∸ suc n) !))
      (choose-diagonal (suc n))
    ∙ cong
        (λ remainder →
          ((suc zero ℕ.· ((suc n) !)) ℕ.· (remainder !)))
        (ℕ.n∸n (suc n))
    ∙ cong (λ value → value ℕ.· suc zero)
        (ℕ.·-identityˡ ((suc n) !))
    ∙ ℕ.·-identityʳ ((suc n) !)
... | inl k+1≤n =
  cong
      (λ complement →
        ((_chooseℕ_ (suc n) (suc k) ℕ.· ((suc k) !))
          ℕ.· (complement !)))
      (sym complement-suc)
  ∙ split-products
  ∙ cong₂ ℕ._+_
      (cong (suc (n ∸ suc k) ℕ.·_)
        (choose-factorial-product n (suc k) k+1≤n))
      (cong (suc k ℕ.·_)
        second-factorial-product)
  ∙ combine-products
  where
  complement-suc :
    suc (n ∸ suc k) ≡ suc n ∸ suc k
  complement-suc = ℕ.≤-∸-suc k+1≤n

  left-coefficient : ℕ
  left-coefficient = _chooseℕ_ n (suc k)

  right-coefficient : ℕ
  right-coefficient = _chooseℕ_ n k

  k-factorial : ℕ
  k-factorial = k !

  remainder-factorial : ℕ
  remainder-factorial = (n ∸ suc k) !

  split-products :
    (((left-coefficient ℕ.+ right-coefficient)
        ℕ.· (suc k ℕ.· k-factorial))
      ℕ.· (suc (n ∸ suc k) ℕ.· remainder-factorial))
    ≡
    (suc (n ∸ suc k) ℕ.·
      ((left-coefficient ℕ.· (suc k ℕ.· k-factorial))
        ℕ.· remainder-factorial))
    ℕ.+
    (suc k ℕ.·
      ((right-coefficient ℕ.· k-factorial)
        ℕ.· (suc (n ∸ suc k) ℕ.· remainder-factorial)))
  split-products =
    split-factorial-products
      left-coefficient right-coefficient k k-factorial
      (n ∸ suc k) remainder-factorial

  second-factorial-product :
    ((_chooseℕ_ n k ℕ.· (k !))
      ℕ.· ((suc (n ∸ suc k)) !))
    ≡ n !
  second-factorial-product =
    cong
      (λ complement →
        ((_chooseℕ_ n k ℕ.· (k !))
          ℕ.· (complement !)))
      complement-suc
    ∙ choose-factorial-product n k (ℕ.<-weaken k+1≤n)

  complement-total :
    suc (n ∸ suc k) ℕ.+ suc k ≡ suc n
  complement-total =
    cong suc (ℕ.≤-∸-+-cancel k+1≤n)

  combine-products :
    (suc (n ∸ suc k) ℕ.· (n !))
      ℕ.+ (suc k ℕ.· (n !))
    ≡ (suc n) !
  combine-products =
    ℕ.·-distribʳ (suc (n ∸ suc k)) (suc k) (n !)
    ∙ cong (ℕ._· (n !)) complement-total


choose-nonzero-below-diagonal : ∀ n k →
  k ℕ.≤ n → ¬ _chooseℕ_ n k ≡ zero
choose-nonzero-below-diagonal n k k≤n choose≡zero =
  ℕ.<→≢ (ℕ.0<! n)
    ( sym (cong
        (λ coefficient →
          (coefficient ℕ.· (k !)) ℕ.· ((n ∸ k) !))
        choose≡zero)
    ∙ choose-factorial-product n k k≤n
    )


-- Exact divided-power coefficient identities -------------------------

choosePositiveRational : ∀ n k →
  k ℕ.≤ n → ℚ₊
choosePositiveRational n k k≤n =
  ℚ.fromNat (_chooseℕ_ n k) , choose-positive
  where
  choose-as-suc :
    suc (ℕ.predℕ (_chooseℕ_ n k)) ≡ _chooseℕ_ n k
  choose-as-suc =
    sym (ℕ.suc-predℕ (_chooseℕ_ n k)
      (choose-nonzero-below-diagonal n k k≤n))

  choose-positive :
    0 ℚ.< ℚ.fromNat (_chooseℕ_ n k)
  choose-positive =
    subst (0 ℚ.<_)
      (cong (λ m → ℚ.fromNat m) choose-as-suc)
      (ℚAbs.0<sucN (ℕ.predℕ (_chooseℕ_ n k)))


chooseFactorialPositiveRational-product : ∀ n k
  (k≤n : k ℕ.≤ n) →
  ((choosePositiveRational n k k≤n ·₊ exponentialRationalFactorial k)
      ·₊ exponentialRationalFactorial (n ∸ k))
    ≡ exponentialRationalFactorial n
chooseFactorialPositiveRational-product n k k≤n =
  ℚ₊≡
    ( cong₂ ℚR._·_
        (cong (ℚR._·_ (ℚ.fromNat (_chooseℕ_ n k)))
          (exponentialRationalFactorial-value k))
        (exponentialRationalFactorial-value (n ∸ k))
    ∙ cong
        (ℚR._· ℚ.fromNat ((n ∸ k) !))
        (ℚAbs.ℕ·→ℚ· (_chooseℕ_ n k) (k !))
    ∙
        (ℚAbs.ℕ·→ℚ·
          (_chooseℕ_ n k ℕ.· (k !)) ((n ∸ k) !))
    ∙ cong (λ m → ℚ.fromNat m)
        (choose-factorial-product n k k≤n)
    ∙ sym (exponentialRationalFactorial-value n)
    )


rationalExponentialCoefficient-product : ∀ n k →
  (k≤n : k ℕ.≤ n) →
  exponentialRationalCoefficient k ℚR.·
      exponentialRationalCoefficient (n ∸ k)
    ≡
  ℚ.fromNat (_chooseℕ_ n k) ℚR.·
      exponentialRationalCoefficient n
rationalExponentialCoefficient-product n k k≤n =
    sym (ℚP.·IdL left)
  ∙ cong (ℚR._· left)
      (sym (ℚInv.x·invℚ₊[x] choose-positive))
  ∙ sym (ℚP.·Assoc choose choose-inverse left)
  ∙ cong (choose ℚR.·_)
      ( ℚP.·Assoc choose-inverse coefficient-k coefficient-rest
      ∙ cong (ℚR._· coefficient-rest)
          (cong fst
            (ℚInv.invℚ₊Dist· choose-positive factorial-k))
      ∙ cong fst
          (ℚInv.invℚ₊Dist·
            (choose-positive ·₊ factorial-k) factorial-rest)
      ∙ cong (fst ∘ _⁻¹₊)
          (chooseFactorialPositiveRational-product n k k≤n)
      )
  where
  choose-positive : ℚ₊
  choose-positive = choosePositiveRational n k k≤n

  factorial-k : ℚ₊
  factorial-k = exponentialRationalFactorial k

  factorial-rest : ℚ₊
  factorial-rest = exponentialRationalFactorial (n ∸ k)

  choose : ℚ
  choose = fst choose-positive

  choose-inverse : ℚ
  choose-inverse = fst (choose-positive ⁻¹₊)

  coefficient-k : ℚ
  coefficient-k = exponentialRationalCoefficient k

  coefficient-rest : ℚ
  coefficient-rest = exponentialRationalCoefficient (n ∸ k)

  left : ℚ
  left = coefficient-k ℚR.· coefficient-rest


exponentialCoefficient-product : ∀ n k →
  (k≤n : k ℕ.≤ n) →
  exponentialCoefficients k · exponentialCoefficients (n ∸ k)
    ≡
  realNatural (_chooseℕ_ n k) · exponentialCoefficients n
exponentialCoefficient-product n k k≤n =
    mul-rat
      (exponentialRationalCoefficient k)
      (exponentialRationalCoefficient (n ∸ k))
  ∙ cong rat
      (rationalExponentialCoefficient-product n k k≤n)
  ∙ sym
      (mul-rat
        (ℚ.fromNat (_chooseℕ_ n k))
        (exponentialRationalCoefficient n))


realBinomialCoefficient-agreesNatural : ∀ n k →
  ℝBinomial._choose_ n k ≡ realNatural (_chooseℕ_ n k)
realBinomialCoefficient-agreesNatural zero zero =
  sym realNatural-one
realBinomialCoefficient-agreesNatural zero (suc k) =
  sym realNatural-zero
realBinomialCoefficient-agreesNatural (suc n) zero =
  sym realNatural-one
realBinomialCoefficient-agreesNatural (suc n) (suc k) =
  cong₂ _+_
    (realBinomialCoefficient-agreesNatural n (suc k))
    (realBinomialCoefficient-agreesNatural n k)
  ∙ sym
      (realNatural-add
        (_chooseℕ_ n (suc k)) (_chooseℕ_ n k))


-- Finite-sum bridges --------------------------------------------------

partialSum-as-finSum : ∀ terms n →
  partialSum terms n ≡
  ℝSum.∑ {n = n} (terms ∘ toℕ)
partialSum-as-finSum terms zero = refl
partialSum-as-finSum terms (suc n) =
  partialSum-first terms n
  ∙ cong (terms zero +_)
      (partialSum-as-finSum (terms ∘ suc) n)


private
  rearrangeExponentialProduct : ∀ a b c d →
    (a · b) · (c · d) ≡ b · ((a · c) · d)
  rearrangeExponentialProduct a b c d =
    cong (_· (c · d)) (mulComm a b)
    ∙ sym (mulAssoc b a (c · d))
    ∙ cong (b ·_) (mulAssoc a c d)


exponentialProductSummand-binomial : ∀ x y n k →
  (k≤n : k ℕ.≤ n) →
  powerSeriesTerms exponentialCoefficients x k ·
      powerSeriesTerms exponentialCoefficients y (n ∸ k)
    ≡
  exponentialCoefficients n ·
    ((ℝBinomial._choose_ n k · powℝ x k) ·
      powℝ y (n ∸ k))
exponentialProductSummand-binomial x y n k k≤n =
    rearrange
      (exponentialCoefficients k)
      (powℝ x k)
      (exponentialCoefficients (n ∸ k))
      (powℝ y (n ∸ k))
  ∙ cong (_· ((powℝ x k) · (powℝ y (n ∸ k))))
      (exponentialCoefficient-product n k k≤n)
  ∙ rearrangeExponentialProduct
      (realNatural (_chooseℕ_ n k))
      (exponentialCoefficients n)
      (powℝ x k)
      (powℝ y (n ∸ k))
  ∙ cong
      (λ coefficient →
        exponentialCoefficients n ·
          ((coefficient · powℝ x k) · powℝ y (n ∸ k)))
      (sym (realBinomialCoefficient-agreesNatural n k))
  where
  rearrange : ∀ a b c d →
    (a · b) · (c · d) ≡ (a · c) · (b · d)
  rearrange a b c d =
    sym (mulAssoc a b (c · d))
    ∙ cong (a ·_) (mulAssoc b c d)
    ∙ cong (λ value → a · (value · d)) (mulComm b c)
    ∙ cong (a ·_) (sym (mulAssoc c b d))
    ∙ mulAssoc a c (b · d)
