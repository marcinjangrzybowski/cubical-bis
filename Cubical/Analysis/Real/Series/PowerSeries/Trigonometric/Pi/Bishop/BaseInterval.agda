module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.BaseInterval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base as ℚ using (ℚ; fromNat)
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚAbs
import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing using (CommRing→Ring)
open import Cubical.Algebra.OrderedCommRing using (OrderedCommRing→Ring)
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Geometric.Rational
  using (two₊; halfℚ; halfℚPath)
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.Signs
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


private
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  positiveIndex : ℕ → ℕ
  positiveIndex zero = suc (suc (suc (suc zero)))
  positiveIndex (suc k) =
    suc (suc (suc (suc (positiveIndex k))))

  cosineTerms : ℝ → RealSequence
  cosineTerms x = powerSeriesTerms cosineCoefficients x

  blockPartialSums : ℝ → RealSequence
  blockPartialSums x k = partialSum (cosineTerms x) (positiveIndex k)


  mutual
    sineRationalSign-addFour : ∀ n →
      sineRationalSign (suc (suc (suc (suc n))))
        ≡ sineRationalSign n
    sineRationalSign-addFour n = ℚ.-Invol (sineRationalSign n)

    cosineRationalSign-addFour : ∀ n →
      cosineRationalSign (suc (suc (suc (suc n))))
        ≡ cosineRationalSign n
    cosineRationalSign-addFour n = ℚ.-Invol (cosineRationalSign n)


  positiveIndex-signs : ∀ k →
    (sineRationalSign (positiveIndex k) ≡ fromNat zero) ×
    (cosineRationalSign (positiveIndex k) ≡ fromNat (suc zero))
  positiveIndex-signs zero = refl , refl
  positiveIndex-signs (suc k) =
    ( sineRationalSign-addFour (positiveIndex k)
      ∙ fst (positiveIndex-signs k)
    , cosineRationalSign-addFour (positiveIndex k)
      ∙ snd (positiveIndex-signs k)
    )


  positiveIndex-above : ∀ k → k ℕ.≤ positiveIndex k
  positiveIndex-above zero = ℕ.zero-≤
  positiveIndex-above (suc k) =
    ℕ.≤-trans
      (ℕ.suc-≤-suc (positiveIndex-above k))
      (ℕ.≤-trans ℕ.≤-sucℕ
        (ℕ.≤-trans ℕ.≤-sucℕ ℕ.≤-sucℕ))


  exponentialCoefficient-nonnegative : ∀ n →
    0ℝ ≤ℝ exponentialCoefficients n
  exponentialCoefficient-nonnegative n =
    invEq
      (rat≤rat≃ (fromNat zero) (exponentialRationalCoefficient n))
      (ℚ.<Weaken≤ (fromNat zero) (exponentialRationalCoefficient n)
        (snd (exponentialRationalFactorial n ℚInv.⁻¹₊)))


  exponentialCoefficient-antitone : ∀ n →
    exponentialCoefficients (suc n) ≤ℝ
      exponentialCoefficients n
  exponentialCoefficient-antitone n =
    subst2 _≤ℝ_
      (mulIdL (exponentialCoefficients (suc n)))
      (exponentialCoefficients-suc n)
      (mulPres≤R-0≤
        1ℝ (realNatural (suc n))
        (exponentialCoefficients (suc n))
        (exponentialCoefficient-nonnegative (suc n))
        (realNatural-mono
          (ℕ.suc-≤-suc ℕ.zero-≤)))


  exponentialTerm-antitone-onUnitInterval : ∀ x n →
    0ℝ ≤ℝ x → x ≤ℝ 1ℝ →
    exponentialCoefficients (suc n) · powℝ x (suc n) ≤ℝ
      exponentialCoefficients n · powℝ x n
  exponentialTerm-antitone-onUnitInterval x n 0≤x x≤1 =
    subst
      (_≤ℝ (exponentialCoefficients n · powℝ x n))
      (sym (mulAssoc
        (exponentialCoefficients (suc n)) x (powℝ x n))
      )
      (mulPres≤R-0≤
        (exponentialCoefficients (suc n) · x)
        (exponentialCoefficients n)
        (powℝ x n)
        (powNonnegative x n 0≤x)
        coefficient-times-x≤previous)
    where
    coefficient-times-x≤previous :
      exponentialCoefficients (suc n) · x ≤ℝ
        exponentialCoefficients n
    coefficient-times-x≤previous =
      ≤ℝ-trans
        (exponentialCoefficients (suc n) · x)
        (exponentialCoefficients (suc n))
        (exponentialCoefficients n)
        (subst
          (exponentialCoefficients (suc n) · x ≤ℝ_)
          (mulIdR (exponentialCoefficients (suc n)))
          (mulPres≤L
            x 1ℝ (exponentialCoefficients (suc n))
            (0≤→isNonnegative
              (exponentialCoefficients (suc n))
              (exponentialCoefficient-nonnegative (suc n)))
            x≤1))
        (exponentialCoefficient-antitone n)


  blockPartialSums→cosine : ∀ x →
    isLimitSequence (blockPartialSums x) (cosℝ x)
  blockPartialSums→cosine x ε = PT.map choose
    (cosinePowerSeriesHasSum x ε)
    where
    choose :
      Σ[ N ∈ ℕ ]
        (∀ n → N ℕ.≤ n →
          partialSum (cosineTerms x) n ∼[ ε ] cosℝ x) →
      Σ[ N ∈ ℕ ]
        (∀ n → N ℕ.≤ n →
          blockPartialSums x n ∼[ ε ] cosℝ x)
    choose (N , tail) =
      N , λ n N≤n →
        tail (positiveIndex n)
          (ℕ.≤-trans N≤n (positiveIndex-above n))


  positiveTerm : ∀ x k →
    cosineTerms x (positiveIndex k) ≡
      exponentialCoefficients (positiveIndex k) ·
        powℝ x (positiveIndex k)
  positiveTerm x k =
    cong (_· powℝ x (positiveIndex k))
      (cosineCoefficient-as-sign (positiveIndex k)
      ∙ cong (_· exponentialCoefficients (positiveIndex k))
          (cong rat (snd (positiveIndex-signs k)))
      ∙ mulIdL (exponentialCoefficients (positiveIndex k)))


  firstZeroTerm : ∀ x k →
    cosineTerms x (suc (positiveIndex k)) ≡ 0ℝ
  firstZeroTerm x k =
    cong (_· powℝ x (suc (positiveIndex k)))
      (cosineCoefficient-as-sign (suc (positiveIndex k))
      ∙ cong (_· exponentialCoefficients (suc (positiveIndex k)))
          (cong rat firstZeroSign)
      ∙ ℝRing.0LeftAnnihilates
          (exponentialCoefficients (suc (positiveIndex k))))
    ∙ ℝRing.0LeftAnnihilates (powℝ x (suc (positiveIndex k)))
    where
    firstZeroSign :
      cosineRationalSign (suc (positiveIndex k)) ≡ fromNat zero
    firstZeroSign =
      cong ℚ.-_ (fst (positiveIndex-signs k))
      ∙ ℚRing.0Selfinverse


  negativeTerm : ∀ x k →
    cosineTerms x (suc (suc (positiveIndex k))) ≡
      - (exponentialCoefficients (suc (suc (positiveIndex k))) ·
          powℝ x (suc (suc (positiveIndex k))))
  negativeTerm x k =
    cong (_· powℝ x (suc (suc (positiveIndex k))))
      (cosineCoefficient-as-sign (suc (suc (positiveIndex k)))
      ∙ cong
          (_· exponentialCoefficients (suc (suc (positiveIndex k))))
          (cong rat negativeSign)
      ∙ negativeOneMul
          (exponentialCoefficients (suc (suc (positiveIndex k)))))
    ∙ ℝRing.-DistL·
        (exponentialCoefficients (suc (suc (positiveIndex k))))
        (powℝ x (suc (suc (positiveIndex k))))
    where
    negativeSign :
      cosineRationalSign (suc (suc (positiveIndex k))) ≡
        ℚ.- fromNat (suc zero)
    negativeSign = cong ℚ.-_ (snd (positiveIndex-signs k))


  secondZeroTerm : ∀ x k →
    cosineTerms x (suc (suc (suc (positiveIndex k)))) ≡ 0ℝ
  secondZeroTerm x k =
    cong (_· powℝ x (suc (suc (suc (positiveIndex k)))))
      (cosineCoefficient-as-sign
          (suc (suc (suc (positiveIndex k))))
      ∙ cong
          (_· exponentialCoefficients
            (suc (suc (suc (positiveIndex k)))))
          (cong rat secondZeroSign)
      ∙ ℝRing.0LeftAnnihilates
          (exponentialCoefficients
            (suc (suc (suc (positiveIndex k))))))
    ∙ ℝRing.0LeftAnnihilates
        (powℝ x (suc (suc (suc (positiveIndex k)))))
    where
    secondZeroSign :
      cosineRationalSign (suc (suc (suc (positiveIndex k)))) ≡
        fromNat zero
    secondZeroSign =
      cong ℚ.-_ (cong ℚ.-_ (fst (positiveIndex-signs k)))
      ∙ ℚ.-Invol (fromNat zero)


  pairedTerms-ordered : ∀ x k →
    0ℝ ≤ℝ x → x ≤ℝ 1ℝ →
    exponentialCoefficients (suc (suc (positiveIndex k))) ·
        powℝ x (suc (suc (positiveIndex k)))
      ≤ℝ
    exponentialCoefficients (positiveIndex k) ·
        powℝ x (positiveIndex k)
  pairedTerms-ordered x k 0≤x x≤1 =
    ≤ℝ-trans
      (exponentialCoefficients (suc (suc (positiveIndex k))) ·
        powℝ x (suc (suc (positiveIndex k))))
      (exponentialCoefficients (suc (positiveIndex k)) ·
        powℝ x (suc (positiveIndex k)))
      (exponentialCoefficients (positiveIndex k) ·
        powℝ x (positiveIndex k))
      (exponentialTerm-antitone-onUnitInterval
        x (suc (positiveIndex k)) 0≤x x≤1)
      (exponentialTerm-antitone-onUnitInterval
        x (positiveIndex k) 0≤x x≤1)


  blockPartialSums-step : ∀ x k →
    0ℝ ≤ℝ x → x ≤ℝ 1ℝ →
    blockPartialSums x k ≤ℝ blockPartialSums x (suc k)
  blockPartialSums-step x k 0≤x x≤1 =
    subst
      (blockPartialSums x k ≤ℝ_)
      (sym blockStepPath)
      pairBound
    where
    positive : ℝ
    positive = exponentialCoefficients (positiveIndex k) ·
      powℝ x (positiveIndex k)
    negative : ℝ
    negative = exponentialCoefficients (suc (suc (positiveIndex k))) ·
      powℝ x (suc (suc (positiveIndex k)))

    pairBound :
      blockPartialSums x k ≤ℝ
        (blockPartialSums x k + positive) + (- negative)
    pairBound =
      subst2 _≤ℝ_
        (cong (blockPartialSums x k +_) (addInvR negative)
          ∙ addIdR (blockPartialSums x k))
        (addAssoc (blockPartialSums x k) positive (- negative))
        (addPres≤L
          (negative + (- negative))
          (positive + (- negative))
          (blockPartialSums x k)
          (addPres≤R negative positive (- negative)
            (pairedTerms-ordered x k 0≤x x≤1)))

    blockStepPath :
      blockPartialSums x (suc k) ≡
        (blockPartialSums x k + positive) + (- negative)
    blockStepPath =
      cong
        (λ z →
          (((blockPartialSums x k + z) +
              cosineTerms x (suc (positiveIndex k))) +
              cosineTerms x (suc (suc (positiveIndex k)))) +
              cosineTerms x (suc (suc (suc (positiveIndex k)))))
        (positiveTerm x k)
      ∙ cong
        (λ z →
          (((blockPartialSums x k + positive) + z) +
              cosineTerms x (suc (suc (positiveIndex k)))) +
              cosineTerms x (suc (suc (suc (positiveIndex k)))))
        (firstZeroTerm x k)
      ∙ cong
        (λ z →
          (((blockPartialSums x k + positive) + 0ℝ) + z) +
            cosineTerms x (suc (suc (suc (positiveIndex k)))))
        (negativeTerm x k)
      ∙ cong
        ((((blockPartialSums x k + positive) + 0ℝ) +
          (- negative)) +_)
        (secondZeroTerm x k)
      ∙ addIdR
          (((blockPartialSums x k + positive) + 0ℝ) + (- negative))
      ∙ cong (_+ (- negative))
          (addIdR (blockPartialSums x k + positive))


  initialBlock≤block : ∀ x k →
    0ℝ ≤ℝ x → x ≤ℝ 1ℝ →
    blockPartialSums x zero ≤ℝ blockPartialSums x k
  initialBlock≤block x zero 0≤x x≤1 =
    ≤ℝ-refl (blockPartialSums x zero)
  initialBlock≤block x (suc k) 0≤x x≤1 =
    ≤ℝ-trans
      (blockPartialSums x zero)
      (blockPartialSums x k)
      (blockPartialSums x (suc k))
      (initialBlock≤block x k 0≤x x≤1)
      (blockPartialSums-step x k 0≤x x≤1)


  initialBlock≤cosine : ∀ x →
    0ℝ ≤ℝ x → x ≤ℝ 1ℝ →
    blockPartialSums x zero ≤ℝ cosℝ x
  initialBlock≤cosine x 0≤x x≤1 =
    eventuallyLowerBoundPresLimit
      {x = blockPartialSums x}
      {l = cosℝ x}
      {b = blockPartialSums x zero}
      (pointwiseLe→eventuallyLe
        {x = λ _ → blockPartialSums x zero}
        {y = blockPartialSums x}
        (λ k → initialBlock≤block x k 0≤x x≤1))
      (blockPartialSums→cosine x)


  initialTermZero : ∀ x → cosineTerms x zero ≡ 1ℝ
  initialTermZero x =
    cong (_· 1ℝ) cosineCoefficients-zero
    ∙ mulIdR 1ℝ

  initialTermOne : ∀ x → cosineTerms x (suc zero) ≡ 0ℝ
  initialTermOne x =
    cong (_· powℝ x (suc zero))
      (cosineCoefficient-as-sign (suc zero)
      ∙ cong (_· exponentialCoefficients (suc zero))
          (cong rat ℚRing.0Selfinverse)
      ∙ ℝRing.0LeftAnnihilates
          (exponentialCoefficients (suc zero)))
    ∙ ℝRing.0LeftAnnihilates (powℝ x (suc zero))

  initialCoefficientTwo :
    cosineCoefficients (suc (suc zero)) ≡ - rat halfℚ
  initialCoefficientTwo = refl

  initialTermTwo : ∀ x →
    cosineTerms x (suc (suc zero)) ≡
      - (rat halfℚ · powℝ x (suc (suc zero)))
  initialTermTwo x =
    cong (_· powℝ x (suc (suc zero))) initialCoefficientTwo
    ∙ ℝRing.-DistL·
        (rat halfℚ) (powℝ x (suc (suc zero)))

  initialTermThree : ∀ x →
    cosineTerms x (suc (suc (suc zero))) ≡ 0ℝ
  initialTermThree x =
    cong (_· powℝ x (suc (suc (suc zero))))
      (cosineCoefficient-as-sign (suc (suc (suc zero)))
      ∙ cong (_· exponentialCoefficients (suc (suc (suc zero))))
          (cong rat (ℚ.-Invol (fromNat zero)))
      ∙ ℝRing.0LeftAnnihilates
          (exponentialCoefficients (suc (suc (suc zero)))))
    ∙ ℝRing.0LeftAnnihilates (powℝ x (suc (suc (suc zero))))


  initialBlockPath : ∀ x →
    blockPartialSums x zero ≡
      1ℝ - rat halfℚ · powℝ x (suc (suc zero))
  initialBlockPath x =
    cong
      (λ z →
        (((0ℝ + z) + cosineTerms x (suc zero)) +
          cosineTerms x (suc (suc zero))) +
          cosineTerms x (suc (suc (suc zero))))
      (initialTermZero x)
    ∙ cong
      (λ z →
        (((0ℝ + 1ℝ) + z) + cosineTerms x (suc (suc zero))) +
          cosineTerms x (suc (suc (suc zero))))
      (initialTermOne x)
    ∙ cong
      (λ z →
        (((0ℝ + 1ℝ) + 0ℝ) + z) +
          cosineTerms x (suc (suc (suc zero))))
      (initialTermTwo x)
    ∙ cong
      ((((0ℝ + 1ℝ) + 0ℝ) +
        (- (rat halfℚ · powℝ x (suc (suc zero))))) +_)
      (initialTermThree x)
    ∙ addIdR
        (((0ℝ + 1ℝ) + 0ℝ) +
          (- (rat halfℚ · powℝ x (suc (suc zero)))))
    ∙ cong (_+ (- (rat halfℚ · powℝ x (suc (suc zero)))))
        (addIdR (0ℝ + 1ℝ))
    ∙ cong (_+ (- (rat halfℚ · powℝ x (suc (suc zero)))))
        (addIdL 1ℝ)


  onePow : ∀ n → powℝ 1ℝ n ≡ 1ℝ
  onePow zero = refl
  onePow (suc n) =
    cong (1ℝ ·_) (onePow n)
    ∙ mulIdL 1ℝ


  halfℚ-double :
    halfℚ ℚ.+ halfℚ ≡ fromNat (suc zero)
  halfℚ-double =
    cong₂ ℚ._+_
      (sym (ℚ.·IdL halfℚ))
      (sym (ℚ.·IdL halfℚ))
    ∙ sym
        (ℚ.·DistR+
          (fromNat (suc zero)) (fromNat (suc zero)) halfℚ)
    ∙ cong (ℚ._· halfℚ)
        (ℚAbs.ℕ+→ℚ+ (suc zero) (suc zero))
    ∙ ℚInv.x·invℚ₊[x] two₊


  one-minus-half : 1ℝ - rat halfℚ ≡ rat halfℚ
  one-minus-half =
    sym (cong (rat halfℚ +_) (addInvR (rat halfℚ)))
    ∙ sym (addAssoc (rat halfℚ) (rat halfℚ) (- rat halfℚ))
    ∙ cong (_+ (- rat halfℚ))
        (rat+rat halfℚ halfℚ ∙ cong rat halfℚ-double)


  halfℝ-nonnegative : 0ℝ ≤ℝ rat halfℚ
  halfℝ-nonnegative =
    invEq (rat≤rat≃ (fromNat zero) halfℚ)
      (ℚ.<Weaken≤ (fromNat zero) halfℚ
        (snd (two₊ ℚInv.⁻¹₊)))


  half≤initialBlock : ∀ x →
    0ℝ ≤ℝ x → x ≤ℝ 1ℝ →
    rat halfℚ ≤ℝ blockPartialSums x zero
  half≤initialBlock x 0≤x x≤1 =
    subst2 _≤ℝ_
      one-minus-half
      (sym (initialBlockPath x))
      (addPres≤L
        (- rat halfℚ)
        (- (rat halfℚ · powℝ x (suc (suc zero))))
        1ℝ
        (negPres≤
          (rat halfℚ · powℝ x (suc (suc zero)))
          (rat halfℚ)
          scaledSquare≤half))
    where
    square≤one :
      powℝ x (suc (suc zero)) ≤ℝ 1ℝ
    square≤one =
      subst
        (powℝ x (suc (suc zero)) ≤ℝ_)
        (onePow (suc (suc zero)))
        (powMono (suc (suc zero)) 0≤x x≤1)

    scaledSquare≤half :
      rat halfℚ · powℝ x (suc (suc zero)) ≤ℝ rat halfℚ
    scaledSquare≤half =
      subst
        (rat halfℚ · powℝ x (suc (suc zero)) ≤ℝ_)
        (mulIdR (rat halfℚ))
        (mulPres≤L
          (powℝ x (suc (suc zero))) 1ℝ (rat halfℚ)
          (0≤→isNonnegative (rat halfℚ) halfℝ-nonnegative)
          square≤one)


cosineQuadraticLowerBound-onUnitInterval : ∀ x →
  0ℝ ≤ℝ x → x ≤ℝ 1ℝ →
  1ℝ - rat halfℚ · powℝ x (suc (suc zero)) ≤ℝ cosℝ x
cosineQuadraticLowerBound-onUnitInterval x 0≤x x≤1 =
  subst
    (_≤ℝ cosℝ x)
    (initialBlockPath x)
    (initialBlock≤cosine x 0≤x x≤1)


half≤cosℝ-onUnitInterval : ∀ x →
  0ℝ ≤ℝ x → x ≤ℝ 1ℝ → rat halfℚ ≤ℝ cosℝ x
half≤cosℝ-onUnitInterval x 0≤x x≤1 =
  ≤ℝ-trans
    (rat halfℚ)
    (blockPartialSums x zero)
    (cosℝ x)
    (half≤initialBlock x 0≤x x≤1)
    (initialBlock≤cosine x 0≤x x≤1)


cosℝ-positive-onUnitInterval : ∀ x →
  0ℝ ≤ℝ x → x ≤ℝ 1ℝ → 0ℝ <ℝ cosℝ x
cosℝ-positive-onUnitInterval x 0≤x x≤1 =
  <≤ℝ-trans
    0ℝ (rat halfℚ) (cosℝ x)
    (<ℚ→<ℝ (fromNat zero) halfℚ (snd (two₊ ℚInv.⁻¹₊)))
    (half≤cosℝ-onUnitInterval x 0≤x x≤1)
