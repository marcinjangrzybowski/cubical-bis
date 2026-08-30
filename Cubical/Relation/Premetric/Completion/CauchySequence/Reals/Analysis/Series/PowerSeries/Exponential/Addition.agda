module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Tactics.NatSolver
open import Cubical.Relation.Nullary

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Data.Nat as ℕ
  using (ℕ ; zero ; suc ; _! ; _∸_)
  renaming
    ( _choose_ to _chooseℕ_
    ; _+_ to _+ℕ_
    ; _·_ to _·ℕ_
    )
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base as ℚ using (ℚ)
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

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Naturals
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Convolution
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.ConvolutionAbsolute
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential


private
  module ℝBinomial = BinomialThm ℝCommRing
  module ℝSum = Sum (CommRing→Ring ℝCommRing)


-- This is the combinatorial core behind multiplication of divided-power
-- series.  Keeping it at the natural-number level separates the finite
-- algebra from all convergence arguments below.

choose-above-offset : ∀ n offset →
  _chooseℕ_ n (suc (offset ℕ.+ n)) ≡ zero
choose-above-offset zero offset =
  refl
choose-above-offset (suc n) offset =
  cong
      (_chooseℕ_ (suc n) ∘ suc)
      (ℕ.+-suc offset n)
  ∙ cong₂ ℕ._+_
      (choose-above-offset n (suc offset))
      (choose-above-offset n offset)


choose-diagonal : ∀ n →
  _chooseℕ_ n n ≡ suc zero
choose-diagonal zero =
  refl
choose-diagonal (suc n) =
  cong₂ ℕ._+_
    (choose-above-offset n zero)
    (choose-diagonal n)


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
  solveℕ!


choose-factorial-product : ∀ n k →
  k ℕ.≤ n →
  ((_chooseℕ_ n k ℕ.· (k !)) ℕ.· ((n ∸ k) !)) ≡ n !
choose-factorial-product zero zero k≤n =
  refl
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
  complement-suc =
    ℕ.≤-∸-suc k+1≤n

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
    ∙ choose-factorial-product n k
        (ℕ.<-weaken k+1≤n)

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


choosePositiveRational : ∀ n k →
  k ℕ.≤ n → ℚ₊
choosePositiveRational n k k≤n =
  naturalRational (_chooseℕ_ n k) , choose-positive
  where
  choose-as-suc :
    suc (ℕ.predℕ (_chooseℕ_ n k)) ≡ _chooseℕ_ n k
  choose-as-suc =
    sym (ℕ.suc-predℕ (_chooseℕ_ n k)
      (choose-nonzero-below-diagonal n k k≤n))

  choose-positive :
    0 ℚ.< naturalRational (_chooseℕ_ n k)
  choose-positive =
    subst (0 ℚ.<_)
      (cong naturalRational choose-as-suc)
      (ℚAbs.0<sucN (ℕ.predℕ (_chooseℕ_ n k)))


chooseFactorialPositiveRational-product : ∀ n k
  (k≤n : k ℕ.≤ n) →
  ((choosePositiveRational n k k≤n ·₊ factorialPositiveRational k)
      ·₊ factorialPositiveRational (n ∸ k))
    ≡ factorialPositiveRational n
chooseFactorialPositiveRational-product n k k≤n =
  ℚ₊≡
    ( cong
        (ℚR._· naturalRational ((n ∸ k) !))
        (sym (ℚAbs.ℕ·→ℚ· (_chooseℕ_ n k) (k !)))
    ∙ sym
        (ℚAbs.ℕ·→ℚ·
          (_chooseℕ_ n k ℕ.· (k !)) ((n ∸ k) !))
    ∙ cong naturalRational
        (choose-factorial-product n k k≤n)
    )


-- Multiplication of divided-power coefficients is the embedded binomial
-- coefficient times the coefficient in total degree.  This is the reusable
-- coefficient identity used by the convolution proof.

rationalExponentialCoefficient-product : ∀ n k →
  (k≤n : k ℕ.≤ n) →
  rationalExponentialCoefficient k ℚR.·
      rationalExponentialCoefficient (n ∸ k)
    ≡
  naturalRational (_chooseℕ_ n k) ℚR.·
      rationalExponentialCoefficient n
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
  factorial-k = factorialPositiveRational k

  factorial-rest : ℚ₊
  factorial-rest = factorialPositiveRational (n ∸ k)

  choose : ℚ
  choose = fst choose-positive

  choose-inverse : ℚ
  choose-inverse = fst (choose-positive ⁻¹₊)

  coefficient-k : ℚ
  coefficient-k = rationalExponentialCoefficient k

  coefficient-rest : ℚ
  coefficient-rest = rationalExponentialCoefficient (n ∸ k)

  left : ℚ
  left = coefficient-k ℚR.· coefficient-rest


exponentialCoefficient-product : ∀ n k →
  (k≤n : k ℕ.≤ n) →
  exponentialCoefficients k Mul.·
      exponentialCoefficients (n ∸ k)
    ≡
  realNatural (_chooseℕ_ n k) Mul.·
      exponentialCoefficients n
exponentialCoefficient-product n k k≤n =
    Mul.mul-ι-ι
      (rationalExponentialCoefficient k)
      (rationalExponentialCoefficient (n ∸ k))
  ∙ cong Real.ιℚ
      (rationalExponentialCoefficient-product n k k≤n)
  ∙ sym
      (Mul.mul-ι-ι
        (naturalRational (_chooseℕ_ n k))
        (rationalExponentialCoefficient n))


realBinomialCoefficient-agreesNatural : ∀ n k →
  ℝBinomial._choose_ n k ≡ realNatural (_chooseℕ_ n k)
realBinomialCoefficient-agreesNatural zero zero =
  sym realNatural-one
realBinomialCoefficient-agreesNatural zero (suc k) =
  sym realNatural-zero
realBinomialCoefficient-agreesNatural (suc n) zero =
  sym realNatural-one
realBinomialCoefficient-agreesNatural (suc n) (suc k) =
  cong₂ Add._+_
    (realBinomialCoefficient-agreesNatural n (suc k))
    (realBinomialCoefficient-agreesNatural n k)
  ∙ sym
      (realNatural-add
        (_chooseℕ_ n (suc k)) (_chooseℕ_ n k))


-- The partial-sum convention and the finite-vector big operation enumerate
-- the same initial segment.  This bridge is useful whenever a polynomial
-- identity from `BigOps` is applied to an analytic series.

partialSum-as-finSum : ∀ terms n →
  partialSum terms n ≡
  ℝSum.∑ {n = n} (terms ∘ toℕ)
partialSum-as-finSum terms zero =
  refl
partialSum-as-finSum terms (suc n) =
  partialSum-first terms n
  ∙ cong (terms zero Add.+_)
      (partialSum-as-finSum (terms ∘ suc) n)


private
  rearrangeExponentialProduct : ∀ a b c d →
    (a Mul.· b) Mul.· (c Mul.· d) ≡
    b Mul.· ((a Mul.· c) Mul.· d)
  rearrangeExponentialProduct a b c d =
    cong (Mul._· (c Mul.· d)) (mul-comm a b)
    ∙ sym (mul-assoc b a (c Mul.· d))
    ∙ cong (b Mul.·_) (mul-assoc a c d)


exponentialProductSummand-binomial : ∀ x y n k →
  (k≤n : k ℕ.≤ n) →
  powerSeriesTerms exponentialCoefficients x k Mul.·
      powerSeriesTerms exponentialCoefficients y (n ∸ k)
    ≡
  exponentialCoefficients n Mul.·
    ((ℝBinomial._choose_ n k Mul.· x ^ⁿ k) Mul.·
      y ^ⁿ (n ∸ k))
exponentialProductSummand-binomial x y n k k≤n =
    rearrange
      (exponentialCoefficients k)
      (x ^ⁿ k)
      (exponentialCoefficients (n ∸ k))
      (y ^ⁿ (n ∸ k))
  ∙ cong (Mul._· ((x ^ⁿ k) Mul.· (y ^ⁿ (n ∸ k))))
      (exponentialCoefficient-product n k k≤n)
  ∙ rearrangeExponentialProduct
      (realNatural (_chooseℕ_ n k))
      (exponentialCoefficients n)
      (x ^ⁿ k)
      (y ^ⁿ (n ∸ k))
  ∙ cong
      (λ coefficient →
        exponentialCoefficients n Mul.·
          ((coefficient Mul.· x ^ⁿ k) Mul.·
            y ^ⁿ (n ∸ k)))
      (sym (realBinomialCoefficient-agreesNatural n k))
  where
  rearrange : ∀ a b c d →
    (a Mul.· b) Mul.· (c Mul.· d) ≡
    (a Mul.· c) Mul.· (b Mul.· d)
  rearrange a b c d =
    sym (mul-assoc a b (c Mul.· d))
    ∙ cong (a Mul.·_) (mul-assoc b c d)
    ∙ cong (λ value → a Mul.· (value Mul.· d))
        (mul-comm b c)
    ∙ cong (a Mul.·_) (sym (mul-assoc c b d))
    ∙ mul-assoc a c (b Mul.· d)


exponentialTerms-cauchyProduct-add : ∀ x y n →
  cauchyProduct
      (powerSeriesTerms exponentialCoefficients x)
      (powerSeriesTerms exponentialCoefficients y) n
    ≡
  powerSeriesTerms exponentialCoefficients (x Add.+ y) n
exponentialTerms-cauchyProduct-add x y n =
    partialSum-pointwiseBefore
      (λ k →
        powerSeriesTerms exponentialCoefficients x k Mul.·
          powerSeriesTerms exponentialCoefficients y (n ∸ k))
      (scaleSeries (exponentialCoefficients n) binomial-terms)
      (suc n)
      (λ k k<sucn →
        exponentialProductSummand-binomial x y n k
          (ℕ.pred-≤-pred k<sucn))
  ∙ partialSum-scale
      (exponentialCoefficients n) binomial-terms (suc n)
  ∙ cong (exponentialCoefficients n Mul.·_)
      (partialSum-as-finSum binomial-terms (suc n))
  ∙ cong (exponentialCoefficients n Mul.·_)
      (sym (ℝBinomial.BinomialThm n x y))
  where
  binomial-terms : RealSequence
  binomial-terms k =
    (ℝBinomial._choose_ n k Mul.· x ^ⁿ k) Mul.·
      y ^ⁿ (n ∸ k)


exponentialTerms-cauchyProduct-add-sequence : ∀ x y →
  cauchyProduct
      (powerSeriesTerms exponentialCoefficients x)
      (powerSeriesTerms exponentialCoefficients y)
    ≡
  powerSeriesTerms exponentialCoefficients (x Add.+ y)
exponentialTerms-cauchyProduct-add-sequence x y =
  funExt (exponentialTerms-cauchyProduct-add x y)


-- Absolute convergence is consumed only to obtain the proposition-valued
-- rectangular approximation required by Mertens.  Its internally chosen
-- rational sum bounds do not escape into the exponential addition law.

exponentialTermsRectangularApproximation : ∀ x y →
  CauchyProductRectangularApproximation
    (powerSeriesTerms exponentialCoefficients x)
    (powerSeriesTerms exponentialCoefficients y)
exponentialTermsRectangularApproximation x y =
  absoluteMertensRectangularApproximation
    (powerSeriesTerms exponentialCoefficients x)
    (powerSeriesTerms exponentialCoefficients y)
    (exponentialPowerSeriesIsAbsolutelyCauchy x)
    (exponentialPowerSeriesIsAbsolutelyCauchy y)


exponentialTermsCauchyProductHasSum : ∀ x y →
  HasSum
    (cauchyProduct
      (powerSeriesTerms exponentialCoefficients x)
      (powerSeriesTerms exponentialCoefficients y))
    (expℝ x Mul.· expℝ y)
exponentialTermsCauchyProductHasSum x y =
  cauchyProductHasSum
    (powerSeriesTerms exponentialCoefficients x)
    (powerSeriesTerms exponentialCoefficients y)
    (expℝ x) (expℝ y)
    (powerSeriesValueHasSum
      exponentialCoefficients x
      (exponentialPowerSeriesIsSummable x))
    (powerSeriesValueHasSum
      exponentialCoefficients y
      (exponentialPowerSeriesIsSummable y))
    (exponentialTermsRectangularApproximation x y)


exponentialAddHasProductSum : ∀ x y →
  HasSum
    (powerSeriesTerms exponentialCoefficients (x Add.+ y))
    (expℝ x Mul.· expℝ y)
exponentialAddHasProductSum x y =
  subst
    (λ terms → HasSum terms (expℝ x Mul.· expℝ y))
    (exponentialTerms-cauchyProduct-add-sequence x y)
    (exponentialTermsCauchyProductHasSum x y)


-- The exponential addition law follows by uniqueness of the native series
-- limit.  Notice that no convergence modulus, rational radius, or global
-- choice of Mertens bounds appears in the statement or proof.

expℝ-add : ∀ x y →
  expℝ (x Add.+ y) ≡ expℝ x Mul.· expℝ y
expℝ-add x y =
  seriesSumIndependent
    (powerSeriesTerms exponentialCoefficients (x Add.+ y))
    (exponentialPowerSeriesIsSummable (x Add.+ y))
    ( expℝ x Mul.· expℝ y
    , exponentialAddHasProductSum x y
    )
