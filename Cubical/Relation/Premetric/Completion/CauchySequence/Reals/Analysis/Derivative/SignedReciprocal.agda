module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.SignedReciprocal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl ; inr)
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Rationals.Base
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Subspace

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Continuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Signed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Reciprocal


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


ApartRealPredicate : ℙ Real.ℝ
ApartRealPredicate = 0＃ₚ


ApartReal : Type₀
ApartReal =
  Σ[ x ∈ Real.ℝ ] x ∈ ApartRealPredicate


ApartRealPremetricSpace :
  PremetricSpace ℓ-zero ℓ-zero
ApartRealPremetricSpace =
  PremetricSubspace Real.ℝPremetricSpace ApartRealPredicate


apartRealCoordinate : ApartReal → Real.ℝ
apartRealCoordinate = fst


apartRealCoordinateIsContinuous :
  isContinuous
    (snd ApartRealPremetricSpace)
    apartRealCoordinate
    (snd Real.ℝPremetricSpace)
apartRealCoordinateIsContinuous =
  snd
    (NE→C
      (subspaceInclusionNE
        Real.ℝPremetricSpace ApartRealPredicate))


-- Apartness is open without choosing a sign globally.  Each branch opens
-- only long enough to construct a propositionally truncated half-gap
-- neighbourhood.  This is the domain fact needed for pointwise quotient
-- rules below: a continuous denominator has an open natural domain.

apartRealPredicateIsOpen :
  IsOpenPredicate
    (snd Real.ℝPremetricSpace)
    ApartRealPredicate
apartRealPredicateIsOpen x =
  ⊎.rec positive-branch negative-branch
  where
  positive-branch :
    Real.ιℚ 0 <ℝ x →
    ∃[ δ ∈ ℚ₊ ]
      (∀ y → x Real.Base.≈ᶜ[ δ ] y →
        Real.ιℚ 0 ＃ y)
  positive-branch =
    PT.map λ gap →
      width gap /2₊
      , λ y x≈y →
          inl
            (positiveGapHalfNeighbourPositive
              x y gap x≈y)

  negative-branch :
    x <ℝ Real.ιℚ 0 →
    ∃[ δ ∈ ℚ₊ ]
      (∀ y → x Real.Base.≈ᶜ[ δ ] y →
        Real.ιℚ 0 ＃ y)
  negative-branch x<0 =
    PT.map
      (λ gap →
        width gap /2₊
        , λ y x≈y →
            inr
              (subst (_<ℝ Real.ιℚ 0)
                (Neg.neg-involutive y)
                (negationOfPositiveNegative
                  (positiveGapHalfNeighbourPositive
                    (Neg.- x) (Neg.- y) gap
                    (Neg.neg-pres≈
                      x y (width gap /2₊) x≈y)))))
      (negativeNegationPositive x<0)


apartRealReciprocal : ApartReal → Real.ℝ
apartRealReciprocal point =
  inverseℝ (fst point) (snd point)


apartRealReciprocalDerivative : ApartReal → Real.ℝ
apartRealReciprocalDerivative point =
  Neg.-
    (apartRealReciprocal point Mul.·
      apartRealReciprocal point)


-- Sign is used only locally.  A half-gap keeps a nearby apart real on the
-- same side of zero, after which continuity is inherited from the positive
-- or negative reciprocal subspace.  No global sign or lower-bound modulus
-- is selected.

apartRealReciprocalIsContinuous :
  isContinuous
    (snd ApartRealPremetricSpace)
    apartRealReciprocal
    (snd Real.ℝPremetricSpace)
apartRealReciprocalIsContinuous x
  .IsContinuousAt.pres≈ ε =
  ⊎.rec positive-branch negative-branch (snd x)
  where
  positive-branch :
    Real.ιℚ 0 <ℝ fst x →
    ∃[ δ ∈ ℚ₊ ]
      (∀ y →
        PremetricStr._≈[_]_
          (snd ApartRealPremetricSpace) x δ y →
        apartRealReciprocal x
          Real.Base.≈ᶜ[ ε ] apartRealReciprocal y)
  positive-branch 0<x =
    PT.rec squash₁ positive-at-gap 0<x
    where
    x-positive : PositiveReal
    x-positive = fst x , 0<x

    positive-at-gap :
      PositiveGap (Real.ιℚ 0) (fst x) →
      ∃[ δ ∈ ℚ₊ ]
        (∀ y →
          PremetricStr._≈[_]_
            (snd ApartRealPremetricSpace) x δ y →
          apartRealReciprocal x
            Real.Base.≈ᶜ[ ε ] apartRealReciprocal y)
    positive-at-gap w =
      PT.map convert-bound
        (positiveRealReciprocalIsContinuous
          x-positive .IsContinuousAt.pres≈ ε)
      where
      half-width : ℚ₊
      half-width = width w /2₊

      convert-bound :
        Σ[ δ ∈ ℚ₊ ]
          (∀ y →
            PremetricStr._≈[_]_
              (snd PositiveRealPremetricSpace) x-positive δ y →
            positiveRealReciprocal x-positive
              Real.Base.≈ᶜ[ ε ] positiveRealReciprocal y)
        →
        Σ[ κ ∈ ℚ₊ ]
          (∀ y →
            PremetricStr._≈[_]_
              (snd ApartRealPremetricSpace) x κ y →
            apartRealReciprocal x
              Real.Base.≈ᶜ[ ε ] apartRealReciprocal y)
      convert-bound (δ , positive-bound) =
        min₊ δ half-width
        , λ y x≈y →
            let
              x≈δy : fst x Real.Base.≈ᶜ[ δ ] fst y
              x≈δy =
                PremetricStr.isMonotone≈≤
                  (snd ApartRealPremetricSpace)
                  x y (min₊ δ half-width) δ
                  (min₊≤L δ half-width) x≈y

              x≈halfy :
                fst x Real.Base.≈ᶜ[ half-width ] fst y
              x≈halfy =
                PremetricStr.isMonotone≈≤
                  (snd ApartRealPremetricSpace)
                  x y (min₊ δ half-width) half-width
                  (min₊≤R δ half-width) x≈y

              y-positive-proof : Real.ιℚ 0 <ℝ fst y
              y-positive-proof =
                positiveGapHalfNeighbourPositive
                  (fst x) (fst y) w x≈halfy

              y-positive : PositiveReal
              y-positive = fst y , y-positive-proof

              function-x-path :
                positiveRealReciprocal x-positive
                  ≡ apartRealReciprocal x
              function-x-path =
                inverseℝProofIrrelevant
                  (fst x) (inl 0<x) (snd x)

              function-y-path :
                positiveRealReciprocal y-positive
                  ≡ apartRealReciprocal y
              function-y-path =
                inverseℝProofIrrelevant
                  (fst y) (inl y-positive-proof) (snd y)
            in
            subst2 (Real.Base._≈ᶜ[ ε ]_)
              function-x-path function-y-path
              (positive-bound y-positive x≈δy)

  negative-branch :
    fst x <ℝ Real.ιℚ 0 →
    ∃[ δ ∈ ℚ₊ ]
      (∀ y →
        PremetricStr._≈[_]_
          (snd ApartRealPremetricSpace) x δ y →
        apartRealReciprocal x
          Real.Base.≈ᶜ[ ε ] apartRealReciprocal y)
  negative-branch x<0 =
    PT.rec squash₁ negative-at-gap (negativeNegationPositive x<0)
    where
    x-negative : NegativeReal
    x-negative = fst x , x<0

    negative-at-gap :
      PositiveGap (Real.ιℚ 0) (Neg.- fst x) →
      ∃[ δ ∈ ℚ₊ ]
        (∀ y →
          PremetricStr._≈[_]_
            (snd ApartRealPremetricSpace) x δ y →
          apartRealReciprocal x
            Real.Base.≈ᶜ[ ε ] apartRealReciprocal y)
    negative-at-gap w =
      PT.map convert-bound
        (negativeRealReciprocalIsContinuous
          x-negative .IsContinuousAt.pres≈ ε)
      where
      half-width : ℚ₊
      half-width = width w /2₊

      convert-bound :
        Σ[ δ ∈ ℚ₊ ]
          (∀ y →
            PremetricStr._≈[_]_
              (snd NegativeRealPremetricSpace) x-negative δ y →
            negativeRealReciprocal x-negative
              Real.Base.≈ᶜ[ ε ] negativeRealReciprocal y)
        →
        Σ[ κ ∈ ℚ₊ ]
          (∀ y →
            PremetricStr._≈[_]_
              (snd ApartRealPremetricSpace) x κ y →
            apartRealReciprocal x
              Real.Base.≈ᶜ[ ε ] apartRealReciprocal y)
      convert-bound (δ , negative-bound) =
        min₊ δ half-width
        , λ y x≈y →
            let
              x≈δy : fst x Real.Base.≈ᶜ[ δ ] fst y
              x≈δy =
                PremetricStr.isMonotone≈≤
                  (snd ApartRealPremetricSpace)
                  x y (min₊ δ half-width) δ
                  (min₊≤L δ half-width) x≈y

              x≈halfy :
                fst x Real.Base.≈ᶜ[ half-width ] fst y
              x≈halfy =
                PremetricStr.isMonotone≈≤
                  (snd ApartRealPremetricSpace)
                  x y (min₊ δ half-width) half-width
                  (min₊≤R δ half-width) x≈y

              negx≈negy :
                (Neg.- fst x)
                  Real.Base.≈ᶜ[ half-width ] (Neg.- fst y)
              negx≈negy =
                Neg.neg-pres≈
                  (fst x) (fst y) half-width x≈halfy

              y-negative-proof : fst y <ℝ Real.ιℚ 0
              y-negative-proof =
                subst (_<ℝ Real.ιℚ 0)
                  (Neg.neg-involutive (fst y))
                  (negationOfPositiveNegative
                    (positiveGapHalfNeighbourPositive
                      (Neg.- fst x) (Neg.- fst y) w negx≈negy))

              y-negative : NegativeReal
              y-negative = fst y , y-negative-proof

              function-x-path :
                negativeRealReciprocal x-negative
                  ≡ apartRealReciprocal x
              function-x-path =
                negativeRealReciprocal≡inverseℝ x-negative
                ∙ inverseℝProofIrrelevant
                    (fst x) (inr x<0) (snd x)

              function-y-path :
                negativeRealReciprocal y-negative
                  ≡ apartRealReciprocal y
              function-y-path =
                negativeRealReciprocal≡inverseℝ y-negative
                ∙ inverseℝProofIrrelevant
                    (fst y) (inr y-negative-proof) (snd y)
            in
            subst2 (Real.Base._≈ᶜ[ ε ]_)
              function-x-path function-y-path
              (negative-bound y-negative x≈δy)


apartRealReciprocalDifferenceFactor :
  ApartReal × ApartReal → Real.ℝ
apartRealReciprocalDifferenceFactor (x , y) =
  Neg.-
    (apartRealReciprocal x Mul.·
      apartRealReciprocal y)


private
  apartRealReciprocalDifferenceFactorization :
    ∀ (x y : ApartReal) →
    apartRealReciprocal y Group.- apartRealReciprocal x
      ≡
    (fst y Group.- fst x) Mul.·
      apartRealReciprocalDifferenceFactor (x , y)
  apartRealReciprocalDifferenceFactorization x y =
    cong₂ Group._-_
      reciprocal-y-as-x-product
      reciprocal-x-as-y-product
    ∙ sym
        (ℝRing.·DistL-
          (fst x) (fst y) reciprocal-product)
    ∙ cong
        (Mul._· reciprocal-product)
        (sym (neg-sub (fst y) (fst x)))
    ∙ ℝRing.-DistL·
        (fst y Group.- fst x) reciprocal-product
    ∙ sym
        (ℝRing.-DistR·
          (fst y Group.- fst x) reciprocal-product)
    where
    reciprocal-x : Real.ℝ
    reciprocal-x = apartRealReciprocal x

    reciprocal-y : Real.ℝ
    reciprocal-y = apartRealReciprocal y

    reciprocal-product : Real.ℝ
    reciprocal-product = reciprocal-x Mul.· reciprocal-y

    reciprocal-y-as-x-product :
      reciprocal-y ≡ fst x Mul.· reciprocal-product
    reciprocal-y-as-x-product =
      sym (mul-one-left reciprocal-y)
      ∙ cong
          (Mul._· reciprocal-y)
          (sym (inverseℝLaw (fst x) (snd x)))
      ∙ sym (mul-assoc (fst x) reciprocal-x reciprocal-y)

    reciprocal-x-as-y-product :
      reciprocal-x ≡ fst y Mul.· reciprocal-product
    reciprocal-x-as-y-product =
      sym (mul-one-right reciprocal-x)
      ∙ cong
          (reciprocal-x Mul.·_)
          (sym (inverseℝLaw (fst y) (snd y)))
      ∙ mul-assoc reciprocal-x (fst y) reciprocal-y
      ∙ cong
          (Mul._· reciprocal-y)
          (mul-comm reciprocal-x (fst y))
      ∙ sym (mul-assoc (fst y) reciprocal-x reciprocal-y)


  apartRealReciprocalDifferenceFactorDiagonal :
    ∀ x →
    apartRealReciprocalDifferenceFactor (x , x)
      ≡ apartRealReciprocalDerivative x
  apartRealReciprocalDifferenceFactorDiagonal x = refl


  apartRealReciprocalDifferenceFactorIsContinuous :
    isContinuous
      (PremetricProductStr
        (snd ApartRealPremetricSpace)
        (snd ApartRealPremetricSpace))
      apartRealReciprocalDifferenceFactor
      (snd Real.ℝPremetricSpace)
  apartRealReciprocalDifferenceFactorIsContinuous =
    snd
      (CategoryStructures._∘C_
        ( Neg.-_
        , isNonExpanding→isContinuous
            (snd Real.ℝPremetricSpace)
            Neg.-_
            (snd Real.ℝPremetricSpace)
            (snd Neg.negationⁿ)
        )
        ( ( λ points →
              apartRealReciprocal (fst points) Mul.·
                apartRealReciprocal (snd points))
        , mulOfContinuousIsContinuous
            (PremetricProductStr
              (snd ApartRealPremetricSpace)
              (snd ApartRealPremetricSpace))
            (apartRealReciprocal ∘ fst)
            (apartRealReciprocal ∘ snd)
            (snd
              (CategoryStructures._∘C_
                ( apartRealReciprocal
                , apartRealReciprocalIsContinuous
                )
                (productFstC
                  {M = ApartRealPremetricSpace}
                  {N = ApartRealPremetricSpace})))
            (snd
              (CategoryStructures._∘C_
                ( apartRealReciprocal
                , apartRealReciprocalIsContinuous
                )
                (productSndC
                  {M = ApartRealPremetricSpace}
                  {N = ApartRealPremetricSpace})))
        ))


apartRealReciprocalHasDerivativeAlong :
  IsDerivativeAlong
    (snd ApartRealPremetricSpace)
    apartRealCoordinate
    apartRealReciprocal
    apartRealReciprocalDerivative
apartRealReciprocalHasDerivativeAlong =
  continuousDifferenceFactorGivesDerivative
    (snd ApartRealPremetricSpace)
    apartRealCoordinate
    apartRealReciprocal
    apartRealReciprocalDerivative
    apartRealReciprocalDifferenceFactor
    apartRealReciprocalDifferenceFactorization
    apartRealReciprocalDifferenceFactorDiagonal
    apartRealReciprocalDifferenceFactorIsContinuous
