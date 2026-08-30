module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric.Tangent where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.OpenPredicate

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Signed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.MultiplicativeApartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Basic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.RationalFunction.Domain
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric.Identities


private
  module TangentAlgebra {ℓ} (R : CommRing ℓ) where
    open CommRingStr (snd R)

    quotient-numerator : ∀ sine cosine inverse →
      ((cosine · cosine) - (sine · (- sine))) ·
          (inverse · inverse)
        ≡
      (cosine · cosine + sine · sine) ·
        (inverse · inverse)
    quotient-numerator sine cosine inverse = solve! R

    secant-quotient-numerator : ∀ sine cosine inverse →
      ((0r · cosine) - (1r · (- sine))) ·
          (inverse · inverse)
        ≡
      (1r · inverse) · (sine · inverse)
    secant-quotient-numerator sine cosine inverse = solve! R

    tangent-times-denominator : ∀ sine cosine inverse →
      cosine · inverse ≡ 1r →
      (sine · inverse) · cosine ≡ sine
    tangent-times-denominator sine cosine inverse law =
        solve! R
      ∙ cong (sine ·_) law
      ∙ ·IdR sine

    secant-square-shape : ∀ inverse →
      (1r · inverse) · (1r · inverse)
        ≡ inverse · inverse
    secant-square-shape inverse = solve! R

    pythagorean-quotient : ∀ sine cosine inverse →
      cosine · inverse ≡ 1r →
      cosine · cosine + sine · sine ≡ 1r →
      1r + (sine · inverse) · (sine · inverse)
        ≡ inverse · inverse
    pythagorean-quotient sine cosine inverse inverse-law pythagorean =
        cong
          (λ value → value + (sine · inverse) · (sine · inverse))
          (sym
            ( cong₂ _·_ inverse-law inverse-law
            ∙ ·IdL 1r))
      ∙ ring-step
      ∙ cong (_· (inverse · inverse)) pythagorean
      ∙ ·IdL (inverse · inverse)
      where
      ring-step :
        (cosine · inverse) · (cosine · inverse) +
            (sine · inverse) · (sine · inverse)
          ≡
        (cosine · cosine + sine · sine) ·
          (inverse · inverse)
      ring-step = solve! R

    negate-product : ∀ sine inverse →
      (- sine) · inverse ≡ - (sine · inverse)
    negate-product sine inverse = solve! R


-- The natural constructive domain of tangent is the open locus where
-- cosine is apart from zero.  Apartness carries a quantitative rational gap,
-- precisely the local information required by the Cauchy-completion inverse.

TangentDomainPredicate : ℙ Real.ℝ
TangentDomainPredicate = ApartDenominatorPredicate cosℝ


TangentDomain : Type₀
TangentDomain = ApartDenominatorDomain cosℝ


TangentDomainPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
TangentDomainPremetricSpace =
  ApartDenominatorDomainPremetricSpace cosℝ


tangentDomainCoordinate : TangentDomain → Real.ℝ
tangentDomainCoordinate = apartDenominatorDomainCoordinate


tangentDomainCoordinateIsContinuous :
  isContinuous
    (snd TangentDomainPremetricSpace)
    tangentDomainCoordinate
    (snd Real.ℝPremetricSpace)
tangentDomainCoordinateIsContinuous =
  apartDenominatorDomainCoordinateIsContinuous cosℝ


tangentDomainPredicateIsOpen :
  IsOpenPredicate
    (snd Real.ℝPremetricSpace)
    TangentDomainPredicate
tangentDomainPredicateIsOpen =
  apartDenominatorPredicateOfDerivativeIsOpen
    cosℝ (Neg.-_ ∘ sinℝ)
    cosℝHasDerivativeNegativeSinℝ


tangentDomainPoint : ∀ x →
  Real.ιℚ 0 ＃ cosℝ x → TangentDomain
tangentDomainPoint x cosine-apart = x , cosine-apart


-- Tangent and secant are defined from the signed reciprocal on the natural
-- domain.  They are therefore insensitive to the particular apartness proof
-- while retaining computational access to the reciprocal laws.

tanℝ : TangentDomain → Real.ℝ
tanℝ = divideOnApartDenominatorDomain sinℝ cosℝ


secℝ : TangentDomain → Real.ℝ
secℝ =
  divideOnApartDenominatorDomain
    (λ _ → Real.ιℚ 1) cosℝ


tanℝ-proofIrrelevant : ∀ x
  (left right : Real.ιℚ 0 ＃ cosℝ x) →
  tanℝ (x , left) ≡ tanℝ (x , right)
tanℝ-proofIrrelevant =
  divideOnApartDenominatorDomain-proofIrrelevant sinℝ cosℝ


secℝ-proofIrrelevant : ∀ x
  (left right : Real.ιℚ 0 ＃ cosℝ x) →
  secℝ (x , left) ≡ secℝ (x , right)
secℝ-proofIrrelevant =
  divideOnApartDenominatorDomain-proofIrrelevant
    (λ _ → Real.ιℚ 1) cosℝ


-- Cancellation laws are public because they are usually a better interface
-- than unfolding the proof-indexed inverse.

tanℝ-mul-cosℝ : ∀ point →
  tanℝ point Mul.· cosℝ (fst point) ≡ sinℝ (fst point)
tanℝ-mul-cosℝ point =
  mulDivideRight
    (sinℝ (fst point)) (cosℝ (fst point)) (snd point)


cosℝ-mul-tanℝ : ∀ point →
  cosℝ (fst point) Mul.· tanℝ point ≡ sinℝ (fst point)
cosℝ-mul-tanℝ point =
    mul-comm (cosℝ (fst point)) (tanℝ point)
  ∙ tanℝ-mul-cosℝ point


secℝ-mul-cosℝ : ∀ point →
  secℝ point Mul.· cosℝ (fst point) ≡ Real.ιℚ 1
secℝ-mul-cosℝ point =
  mulDivideRight
    (Real.ιℚ 1) (cosℝ (fst point)) (snd point)


cosℝ-mul-secℝ : ∀ point →
  cosℝ (fst point) Mul.· secℝ point ≡ Real.ιℚ 1
cosℝ-mul-secℝ point =
    mul-comm (cosℝ (fst point)) (secℝ point)
  ∙ secℝ-mul-cosℝ point


-- The normalized quotient rule collapses to secant squared.  The collapse
-- uses the global Pythagorean identity, so the final derivative contains no
-- subtraction and exposes the positive-square shape needed by later order
-- arguments.

tanℝDerivative : TangentDomain → Real.ℝ
tanℝDerivative point =
  inverseℝ (cosℝ (fst point)) (snd point) Mul.·
    inverseℝ (cosℝ (fst point)) (snd point)


private
  tanℝRawDerivative : TangentDomain → Real.ℝ
  tanℝRawDerivative =
    divideOnApartDenominatorDomainDerivative
      sinℝ cosℝ cosℝ (Neg.-_ ∘ sinℝ)


tanℝRawDerivative≡tanℝDerivative :
  tanℝRawDerivative ≡ tanℝDerivative
tanℝRawDerivative≡tanℝDerivative =
  funExt λ point →
      TangentAlgebra.quotient-numerator ℝCommRing
        (sinℝ (fst point))
        (cosℝ (fst point))
        (inverseℝ (cosℝ (fst point)) (snd point))
    ∙ cong
        (Mul._·
          (inverseℝ (cosℝ (fst point)) (snd point) Mul.·
            inverseℝ (cosℝ (fst point)) (snd point)))
        (cosSquare-add-sinSquare≡one (fst point))
    ∙ mul-one-left
        (inverseℝ (cosℝ (fst point)) (snd point) Mul.·
          inverseℝ (cosℝ (fst point)) (snd point))


tanℝHasDerivativeSecantSquared :
  IsDerivativeAlong
    (snd TangentDomainPremetricSpace)
    tangentDomainCoordinate
    tanℝ
    tanℝDerivative
tanℝHasDerivativeSecantSquared =
  subst
    (IsDerivativeAlong
      (snd TangentDomainPremetricSpace)
      tangentDomainCoordinate
      tanℝ)
    tanℝRawDerivative≡tanℝDerivative
    (divideOnApartDenominatorDomainHasDerivativeAlong
      sinℝ cosℝ cosℝ (Neg.-_ ∘ sinℝ)
      sinℝHasDerivativeCosℝ
      cosℝHasDerivativeNegativeSinℝ)


secℝSquared : TangentDomain → Real.ℝ
secℝSquared point = secℝ point Mul.· secℝ point


tanℝDerivative≡secℝSquared :
  tanℝDerivative ≡ secℝSquared
tanℝDerivative≡secℝSquared =
  funExt λ point →
    sym
      (TangentAlgebra.secant-square-shape ℝCommRing
        (inverseℝ (cosℝ (fst point)) (snd point)))


tanℝHasDerivativeSecℝSquared :
  IsDerivativeAlong
    (snd TangentDomainPremetricSpace)
    tangentDomainCoordinate
    tanℝ
    secℝSquared
tanℝHasDerivativeSecℝSquared =
  subst
    (IsDerivativeAlong
      (snd TangentDomainPremetricSpace)
      tangentDomainCoordinate
      tanℝ)
    tanℝDerivative≡secℝSquared
    tanℝHasDerivativeSecantSquared


tanℝDerivative≡onePlusSquare : ∀ point →
  tanℝDerivative point ≡
    Real.ιℚ 1 Add.+ (tanℝ point Mul.· tanℝ point)
tanℝDerivative≡onePlusSquare point =
  sym
    (TangentAlgebra.pythagorean-quotient ℝCommRing
      (sinℝ (fst point))
      (cosℝ (fst point))
      (inverseℝ (cosℝ (fst point)) (snd point))
      (inverseℝLaw (cosℝ (fst point)) (snd point))
      (cosSquare-add-sinSquare≡one (fst point)))


-- Secant differentiates to secant times tangent on the same natural domain.

secℝDerivative : TangentDomain → Real.ℝ
secℝDerivative point = secℝ point Mul.· tanℝ point


private
  secℝRawDerivative : TangentDomain → Real.ℝ
  secℝRawDerivative =
    divideOnApartDenominatorDomainDerivative
      (λ _ → Real.ιℚ 1) cosℝ
      (λ _ → Real.ιℚ 0) (Neg.-_ ∘ sinℝ)


secℝRawDerivative≡secℝDerivative :
  secℝRawDerivative ≡ secℝDerivative
secℝRawDerivative≡secℝDerivative =
  funExt λ point →
    TangentAlgebra.secant-quotient-numerator ℝCommRing
      (sinℝ (fst point))
      (cosℝ (fst point))
      (inverseℝ (cosℝ (fst point)) (snd point))


secℝHasDerivativeSecℝMulTanℝ :
  IsDerivativeAlong
    (snd TangentDomainPremetricSpace)
    tangentDomainCoordinate
    secℝ
    secℝDerivative
secℝHasDerivativeSecℝMulTanℝ =
  subst
    (IsDerivativeAlong
      (snd TangentDomainPremetricSpace)
      tangentDomainCoordinate
      secℝ)
    secℝRawDerivative≡secℝDerivative
    (divideOnApartDenominatorDomainHasDerivativeAlong
      (λ _ → Real.ιℚ 1) cosℝ
      (λ _ → Real.ιℚ 0) (Neg.-_ ∘ sinℝ)
      (constantHasDerivative (Real.ιℚ 1))
      cosℝHasDerivativeNegativeSinℝ)


-- Negation preserves the natural domain because cosine is even.  Packaging
-- it as a non-expanding involution makes parity usable in later subspace
-- constructions without rebuilding metric transport.

negateTangentDomain : TangentDomain → TangentDomain
negateTangentDomain point =
  Neg.- fst point
  , subst
      (Real.ιℚ 0 ＃_)
      (sym (cosℝ-neg (fst point)))
      (snd point)


negateTangentDomainNE :
  NE[ TangentDomainPremetricSpace , TangentDomainPremetricSpace ]
fst negateTangentDomainNE = negateTangentDomain
negateTangentDomainNE .snd .IsNonExpanding.pres≈
  point other ε point≈other =
    Neg.neg-pres≈ (fst point) (fst other) ε point≈other


negateTangentDomain-involutive : ∀ point →
  negateTangentDomain (negateTangentDomain point) ≡ point
negateTangentDomain-involutive point =
  Σ≡Prop
    (λ x → isProp＃ (Real.ιℚ 0) (cosℝ x))
    (Neg.neg-involutive (fst point))


private
  inverseCosineAtNegation : ∀ point →
    inverseℝ
        (cosℝ (Neg.- fst point))
        (snd (negateTangentDomain point))
      ≡
    inverseℝ (cosℝ (fst point)) (snd point)
  inverseCosineAtNegation point =
    cong
      (λ apart-real → inverseℝ (fst apart-real) (snd apart-real))
      (Σ≡Prop
        (λ value → isProp＃ (Real.ιℚ 0) value)
        {u =
          cosℝ (Neg.- fst point)
          , snd (negateTangentDomain point)}
        {v = cosℝ (fst point) , snd point}
        (cosℝ-neg (fst point)))


tanℝ-neg : ∀ point →
  tanℝ (negateTangentDomain point) ≡ Neg.- tanℝ point
tanℝ-neg point =
    cong
      (Mul._·
        inverseℝ
          (cosℝ (Neg.- fst point))
          (snd (negateTangentDomain point)))
      (sinℝ-neg (fst point))
  ∙ cong
      ((Neg.- sinℝ (fst point)) Mul.·_)
      (inverseCosineAtNegation point)
  ∙ TangentAlgebra.negate-product ℝCommRing
      (sinℝ (fst point))
      (inverseℝ (cosℝ (fst point)) (snd point))


secℝ-neg : ∀ point →
  secℝ (negateTangentDomain point) ≡ secℝ point
secℝ-neg point =
  cong
    (Real.ιℚ 1 Mul.·_)
    (inverseCosineAtNegation point)


zeroTangentDomain : TangentDomain
zeroTangentDomain =
  Real.ιℚ 0
  , subst
      (Real.ιℚ 0 ＃_)
      (sym cosℝ-zero)
      apartOne


tanℝ-zero : tanℝ zeroTangentDomain ≡ Real.ιℚ 0
tanℝ-zero =
    cong
      (Mul._·
        inverseℝ (cosℝ (Real.ιℚ 0)) (snd zeroTangentDomain))
      sinℝ-zero
  ∙ mul-zero-left
      (inverseℝ (cosℝ (Real.ιℚ 0)) (snd zeroTangentDomain))


secℝ-zero : secℝ zeroTangentDomain ≡ Real.ιℚ 1
secℝ-zero =
    sym (mul-one-right (secℝ zeroTangentDomain))
  ∙ cong (secℝ zeroTangentDomain Mul.·_) (sym cosℝ-zero)
  ∙ secℝ-mul-cosℝ zeroTangentDomain
