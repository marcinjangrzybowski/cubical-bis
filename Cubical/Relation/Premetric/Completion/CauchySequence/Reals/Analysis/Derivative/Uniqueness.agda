module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Uniqueness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

open import Cubical.Data.Rationals.Base as ℚData
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.Rationals using (ℚPremetricSpace)

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Continuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (abs-triangle ; add-monotone)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (abs-mul ; mul-preserves≤-right-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Positive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Order
  using (positiveReciprocalPositive)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (absDifference<→closeness)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)
  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)

  differenceOfSums :
    ∀ (a b c d : Real.ℝ) →
    (a Add.+ b) Group.- (c Add.+ d)
      ≡
    (a Group.- c) Add.+ (b Group.- d)
  differenceOfSums a b c d =
      cong ((a Add.+ b) Add.+_) (neg-add c d)
    ∙ sym (add-assoc a b ((Neg.- c) Add.+ (Neg.- d)))
    ∙ cong (a Add.+_) (add-assoc b (Neg.- c) (Neg.- d))
    ∙ cong (λ value → a Add.+ (value Add.+ (Neg.- d)))
        (add-comm b (Neg.- c))
    ∙ cong (a Add.+_)
        (sym (add-assoc (Neg.- c) b (Neg.- d)))
    ∙ add-assoc a (Neg.- c) (b Add.+ (Neg.- d))

  differenceOfNegatives : ∀ a b →
    (Neg.- a) Group.- (Neg.- b) ≡ Neg.- (a Group.- b)
  differenceOfNegatives a b =
      cong ((Neg.- a) Add.+_) (Neg.neg-involutive b)
    ∙ add-comm (Neg.- a) b
    ∙ sym (neg-sub a b)

  derivativeErrorDifferencePath :
    ∀ (function : Real.ℝ → Real.ℝ) (x y a b : Real.ℝ) →
    ((function y Group.- function x) Group.-
        (b Mul.· (y Group.- x))) Group.-
      ((function y Group.- function x) Group.-
        (a Mul.· (y Group.- x)))
      ≡
    (a Group.- b) Mul.· (y Group.- x)
  derivativeErrorDifferencePath function x y a b =
      differenceOfSums
        difference (Neg.- (b Mul.· displacement))
        difference (Neg.- (a Mul.· displacement))
    ∙ cong₂ Add._+_
        (sub-self difference)
        (differenceOfNegatives
            (b Mul.· displacement) (a Mul.· displacement)
        ∙ neg-sub
            (b Mul.· displacement) (a Mul.· displacement))
    ∙ add-zero-left
        ((a Mul.· displacement) Group.- (b Mul.· displacement))
    ∙ sym (ℝRing.·DistL- a b displacement)
    where
    difference : Real.ℝ
    difference = function y Group.- function x

    displacement : Real.ℝ
    displacement = y Group.- x


  positiveMulCancelRight≤ : ∀ a b c →
    Real.ιℚ 0 <ℝ c →
    (a Mul.· c) ≤ℝ (b Mul.· c) →
    a ≤ℝ b
  positiveMulCancelRight≤ a b c 0<c ac≤bc =
    subst2 _≤ℝ_
      (cancel-path a) (cancel-path b)
      (mul-preserves≤-right-nonnegative
        (a Mul.· c) (b Mul.· c)
        (positiveReciprocal c 0<c)
        ac≤bc
        (<ℝ-weaken
          (Real.ιℚ 0) (positiveReciprocal c 0<c)
          (positiveReciprocalPositive c 0<c)))
    where
    cancel-path : ∀ value →
      (value Mul.· c) Mul.· positiveReciprocal c 0<c ≡ value
    cancel-path value =
        sym (mul-assoc value c (positiveReciprocal c 0<c))
      ∙ cong (value Mul.·_) (positiveReciprocalLaw c 0<c)
      ∙ mul-one-right value


  positiveIncrementDistance : ∀ x (h : ℚ₊) →
    Abs.absℝ
      ((x Add.+ Real.ιℚ (fst h)) Group.- x)
      ≡
    Real.ιℚ (fst h)
  positiveIncrementDistance x h =
      cong Abs.absℝ
        (cong (Group._- x)
            (add-comm x (Real.ιℚ (fst h)))
        ∙ add-sub-cancel (Real.ιℚ (fst h)) x)
    ∙ Abs.absℝ-ι (fst h)
    ∙ cong Real.ιℚ
        (ℚOrder.0<→abs≡id (fst h) (snd h))


  zeroPositiveDistance : ∀ (h : ℚ₊) →
    ℚOrder.abs (0 ℚR.- fst h) ≡ fst h
  zeroPositiveDistance h =
      ℚOrder.abs-Comm 0 (fst h)
    ∙ cong ℚOrder.abs
        (cong (fst h ℚR.+_) ℚRing.0Selfinverse
        ∙ ℚR.+IdR (fst h))
    ∙ ℚOrder.0<→abs≡id (fst h) (snd h)


  closeToPositiveIncrement : ∀ x (h δ : ℚ₊) →
    h <₊ δ →
    x Real.Base.≈ᶜ[ δ ] (x Add.+ Real.ιℚ (fst h))
  closeToPositiveIncrement x h δ h<δ =
    subst
      (λ left →
        left Real.Base.≈ᶜ[ δ ]
          (x Add.+ Real.ιℚ (fst h)))
      (add-zero-right x)
      (add-pres≈₂
        x (Real.ιℚ 0) (Real.ιℚ (fst h)) δ
        (Real.Base.ι-ι 0 (fst h) δ
          (subst
            (ℚ._< fst δ)
            (sym (zeroPositiveDistance h)) h<δ)))


  absSubTriangle : ∀ a b →
    Abs.absℝ (a Group.- b) ≤ℝ
      Abs.absℝ a Add.+ Abs.absℝ b
  absSubTriangle a b =
    subst
      (Abs.absℝ (a Group.- b) ≤ℝ_)
      (cong (Abs.absℝ a Add.+_) (Abs.absℝ-neg b))
      (abs-triangle a (Neg.- b))


  derivativeValuesCloseFromModuli :
    ∀ (function : Real.ℝ → Real.ℝ) (x a b : Real.ℝ)
      (ε δa δb : ℚ₊) →
    (∀ y → x Real.Base.≈ᶜ[ δa ] y →
      Abs.absℝ
        ((function y Group.- function x) Group.-
          (a Mul.· (y Group.- x)))
        ≤ℝ
      Real.ιℚ (fst (ε /4₊)) Mul.·
        Abs.absℝ (y Group.- x)) →
    (∀ y → x Real.Base.≈ᶜ[ δb ] y →
      Abs.absℝ
        ((function y Group.- function x) Group.-
          (b Mul.· (y Group.- x)))
        ≤ℝ
      Real.ιℚ (fst (ε /4₊)) Mul.·
        Abs.absℝ (y Group.- x)) →
    a Real.Base.≈ᶜ[ ε ] b
  derivativeValuesCloseFromModuli
    function x a b ε δa δb
    a-error-near b-error-near =
    absDifference<→closeness a b ε
      (≤<ℝ-trans
        (Abs.absℝ (a Group.- b))
        (Real.ιℚ (fst (ε /2₊)))
        (Real.ιℚ (fst ε))
        slope-difference-bound
        (<ℚ→<ℝ
          (fst (ε /2₊)) (fst ε) (/2₊<id ε)))
    where
    common : ℚ₊
    common = min₊ δa δb

    h : ℚ₊
    h = common /2₊

    y : Real.ℝ
    y = x Add.+ Real.ιℚ (fst h)

    displacement : Real.ℝ
    displacement = y Group.- x

    distance : Real.ℝ
    distance = Abs.absℝ displacement

    a-error b-error : Real.ℝ
    a-error =
      (function y Group.- function x) Group.-
        (a Mul.· displacement)
    b-error =
      (function y Group.- function x) Group.-
        (b Mul.· displacement)

    h<δa : h <₊ δa
    h<δa =
      ℚ.isTrans<≤
        (fst h) (fst common) (fst δa)
        (/2₊<id common) (min₊≤L δa δb)

    h<δb : h <₊ δb
    h<δb =
      ℚ.isTrans<≤
        (fst h) (fst common) (fst δb)
        (/2₊<id common) (min₊≤R δa δb)

    a-error-bound :
      Abs.absℝ a-error ≤ℝ
        Real.ιℚ (fst (ε /4₊)) Mul.· distance
    a-error-bound =
      a-error-near y
        (closeToPositiveIncrement x h δa h<δa)

    b-error-bound :
      Abs.absℝ b-error ≤ℝ
        Real.ιℚ (fst (ε /4₊)) Mul.· distance
    b-error-bound =
      b-error-near y
        (closeToPositiveIncrement x h δb h<δb)

    half-bound-path :
      (Real.ιℚ (fst (ε /4₊)) Mul.· distance) Add.+
          (Real.ιℚ (fst (ε /4₊)) Mul.· distance)
        ≡
      Real.ιℚ (fst (ε /2₊)) Mul.· distance
    half-bound-path =
        sym
          (mul-distrib-over-add-left
            (Real.ιℚ (fst (ε /4₊)))
            (Real.ιℚ (fst (ε /4₊))) distance)
      ∙ cong (Mul._· distance)
          (Add.add-ι-ι (fst (ε /4₊)) (fst (ε /4₊))
          ∙ cong Real.ιℚ (/4+/4≡/2 (fst ε)))

    slope-product-bound :
      Abs.absℝ ((a Group.- b) Mul.· displacement)
        ≤ℝ
      Real.ιℚ (fst (ε /2₊)) Mul.· distance
    slope-product-bound =
      subst
        (λ value →
          Abs.absℝ value ≤ℝ
            Real.ιℚ (fst (ε /2₊)) Mul.· distance)
        (derivativeErrorDifferencePath function x y a b)
        (≤ℝ-trans
          (Abs.absℝ (b-error Group.- a-error))
          (Abs.absℝ b-error Add.+ Abs.absℝ a-error)
          (Real.ιℚ (fst (ε /2₊)) Mul.· distance)
          (absSubTriangle b-error a-error)
          (subst
            ((Abs.absℝ b-error Add.+ Abs.absℝ a-error) ≤ℝ_)
            half-bound-path
            (add-monotone
              (Abs.absℝ b-error)
              (Real.ιℚ (fst (ε /4₊)) Mul.· distance)
              (Abs.absℝ a-error)
              (Real.ιℚ (fst (ε /4₊)) Mul.· distance)
              b-error-bound a-error-bound)))

    absolute-product-bound :
      Abs.absℝ (a Group.- b) Mul.· distance
        ≤ℝ
      Real.ιℚ (fst (ε /2₊)) Mul.· distance
    absolute-product-bound =
      subst
        (_≤ℝ Real.ιℚ (fst (ε /2₊)) Mul.· distance)
        (abs-mul (a Group.- b) displacement)
        slope-product-bound

    distance-positive : Real.ιℚ 0 <ℝ distance
    distance-positive =
      subst
        (Real.ιℚ 0 <ℝ_)
        (sym (positiveIncrementDistance x h))
        (<ℚ→<ℝ 0 (fst h) (snd h))

    slope-difference-bound :
      Abs.absℝ (a Group.- b) ≤ℝ
        Real.ιℚ (fst (ε /2₊))
    slope-difference-bound =
      positiveMulCancelRight≤
        (Abs.absℝ (a Group.- b))
        (Real.ιℚ (fst (ε /2₊)))
        distance distance-positive absolute-product-bound


isPropIsDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → Real.ℝ) →
  isProp (IsDerivativeAlong source coordinate function derivative)
isPropIsDerivativeAlong source coordinate function derivative =
  isPropΠ2 λ _ _ → squash₁


isPropIsDerivative : ∀ function derivative →
  isProp (IsDerivative function derivative)
isPropIsDerivative function derivative =
  isPropIsDerivativeAlong
    (snd Real.ℝPremetricSpace)
    (idfun Real.ℝ) function derivative


isPropIsDerivativeAt : ∀ function derivative-value x →
  isProp (IsDerivativeAt function derivative-value x)
isPropIsDerivativeAt function derivative-value x =
  isPropΠ λ _ → squash₁


derivativeValueUniqueAt : ∀ function x a b →
  IsDerivativeAt function a x →
  IsDerivativeAt function b x →
  a ≡ b
derivativeValueUniqueAt
  function x a b a-derivative b-derivative =
  PremetricStr.isSeparated≈
    (snd Real.ℝPremetricSpace) a b λ ε →
      PT.rec
        (Real.Base.isProp≈ᶜ a ε b)
        (λ a-modulus →
          PT.rec
            (Real.Base.isProp≈ᶜ a ε b)
            (λ b-modulus →
              derivativeValuesCloseFromModuli
                function x a b ε
                (fst a-modulus) (fst b-modulus)
                (snd a-modulus) (snd b-modulus))
            (b-derivative (ε /4₊)))
        (a-derivative (ε /4₊))


derivativeValueUnique :
  ∀ function derivative₁ derivative₂ →
  IsDerivative function derivative₁ →
  IsDerivative function derivative₂ →
  ∀ x → derivative₁ x ≡ derivative₂ x
derivativeValueUnique
  function derivative₁ derivative₂
  first-derivative second-derivative x =
  derivativeValueUniqueAt
    function x (derivative₁ x) (derivative₂ x)
    (first-derivative x) (second-derivative x)


derivativeFunctionUnique :
  ∀ function derivative₁ derivative₂ →
  IsDerivative function derivative₁ →
  IsDerivative function derivative₂ →
  derivative₁ ≡ derivative₂
derivativeFunctionUnique
  function derivative₁ derivative₂ first-derivative second-derivative =
  funExt
    (derivativeValueUnique
      function derivative₁ derivative₂
      first-derivative second-derivative)


HasDerivative : (Real.ℝ → Real.ℝ) → Type
HasDerivative function =
  Σ[ derivative ∈ (Real.ℝ → Real.ℝ) ]
    IsDerivative function derivative


isPropHasDerivative : ∀ function → isProp (HasDerivative function)
isPropHasDerivative function
  (derivative₁ , first-derivative)
  (derivative₂ , second-derivative) =
  ΣPathPProp
    (isPropIsDerivative function)
    (derivativeFunctionUnique
      function derivative₁ derivative₂
      first-derivative second-derivative)


HasDerivativeAt : (Real.ℝ → Real.ℝ) → Real.ℝ → Type
HasDerivativeAt function x =
  Σ[ derivative-value ∈ Real.ℝ ]
    IsDerivativeAt function derivative-value x


isPropHasDerivativeAt : ∀ function x →
  isProp (HasDerivativeAt function x)
isPropHasDerivativeAt function x
  (a , a-derivative) (b , b-derivative) =
  ΣPathPProp
    (λ derivative-value →
      isPropIsDerivativeAt function derivative-value x)
    (derivativeValueUniqueAt
      function x a b a-derivative b-derivative)
