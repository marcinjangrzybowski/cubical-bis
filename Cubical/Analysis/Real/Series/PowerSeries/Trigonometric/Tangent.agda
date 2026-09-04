module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Inverse.Signed
open import Cubical.Analysis.Real.Order.Apartness
open import Cubical.Analysis.Real.Order.MultiplicativeApartness
open import
  Cubical.Analysis.Real.Calculus.Derivative.RationalFunction.Domain
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)

-- Tangent is partial constructively: its point carries the quantitative
-- evidence that cosine is apart from zero.  This avoids assigning arbitrary
-- values at poles and makes every cancellation law total on the domain.

TangentDomainPredicate : ℙ ℝ
TangentDomainPredicate = ApartDenominatorPredicate cosℝ


TangentDomain : Type
TangentDomain = ApartDenominatorDomain cosℝ


TangentDomainPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
TangentDomainPremetricSpace =
  ApartDenominatorDomainPremetricSpace cosℝ


tangentDomainCoordinate : TangentDomain → ℝ
tangentDomainCoordinate = apartDenominatorDomainCoordinate


tangentDomainCoordinateIsContinuous :
  isContinuous
    (TangentDomainPremetricSpace .snd)
    tangentDomainCoordinate
    (ℝPremetricSpace .snd)
tangentDomainCoordinateIsContinuous =
  apartDenominatorDomainCoordinateIsContinuous cosℝ


tangentDomainPoint : ∀ x →
  0ℝ #ℝ cosℝ x → TangentDomain
tangentDomainPoint x cosine-apart = x , cosine-apart


opaque
  cosℝ-zero-for-tangent : cosℝ 0ℝ ≡ 1ℝ
  cosℝ-zero-for-tangent = cosℝ-zero


opaque
  sinℝ-zero-for-tangent : sinℝ 0ℝ ≡ 0ℝ
  sinℝ-zero-for-tangent = sinℝ-zero


opaque
  cosineAtZeroApart : 0ℝ #ℝ cosℝ 0ℝ
  cosineAtZeroApart =
    subst
      (0ℝ #ℝ_)
      (sym cosℝ-zero-for-tangent)
      apartOne


opaque
  tangentDomainZero : TangentDomain
  tangentDomainZero =
    0ℝ , cosineAtZeroApart


  tangentDomainZero-coordinate :
    fst tangentDomainZero ≡ 0ℝ
  tangentDomainZero-coordinate = refl


opaque
  tanℝ : TangentDomain → ℝ
  tanℝ = divideOnApartDenominatorDomain sinℝ cosℝ


  secℝ : TangentDomain → ℝ
  secℝ =
    divideOnApartDenominatorDomain
      (λ _ → 1ℝ) cosℝ


  tanℝ-definingEquation : ∀ point →
    tanℝ point ≡
    divideℝ
      (sinℝ (fst point))
      (cosℝ (fst point))
      (snd point)
  tanℝ-definingEquation point = refl


  secℝ-definingEquation : ∀ point →
    secℝ point ≡
    divideℝ
      1ℝ
      (cosℝ (fst point))
      (snd point)
  secℝ-definingEquation point = refl


  tanℝ-proofIrrelevant : ∀ x
    (left right : 0ℝ #ℝ cosℝ x) →
    tanℝ (x , left) ≡ tanℝ (x , right)
  tanℝ-proofIrrelevant =
    divideOnApartDenominatorDomain-proofIrrelevant sinℝ cosℝ


  secℝ-proofIrrelevant : ∀ x
    (left right : 0ℝ #ℝ cosℝ x) →
    secℝ (x , left) ≡ secℝ (x , right)
  secℝ-proofIrrelevant =
    divideOnApartDenominatorDomain-proofIrrelevant
      (λ _ → 1ℝ) cosℝ


  tanℝ-mul-cosℝ : ∀ point →
    tanℝ point · cosℝ (fst point) ≡ sinℝ (fst point)
  tanℝ-mul-cosℝ point =
    mulDivideRight
      (sinℝ (fst point)) (cosℝ (fst point)) (snd point)


  secℝ-mul-cosℝ : ∀ point →
    secℝ point · cosℝ (fst point) ≡ 1ℝ
  secℝ-mul-cosℝ point =
    mulDivideRight
      1ℝ (cosℝ (fst point)) (snd point)


  divideZeroOnTangentDomain : ∀ point →
    divideℝ
      0ℝ (cosℝ (fst point)) (snd point)
      ≡ 0ℝ
  divideZeroOnTangentDomain point =
    ℝRing.0LeftAnnihilates
      (inverseℝ (cosℝ (fst point)) (snd point))


  divideOnTangentDomainPresNumerator : ∀ point x y →
    x ≡ y →
    divideℝ x (cosℝ (fst point)) (snd point)
      ≡
    divideℝ y (cosℝ (fst point)) (snd point)
  divideOnTangentDomainPresNumerator point x y x≡y =
    cong
      (_· inverseℝ (cosℝ (fst point)) (snd point))
      x≡y


  tanℝ-zero-from-sine-zero : ∀ point →
    sinℝ (fst point) ≡ 0ℝ → tanℝ point ≡ 0ℝ
  tanℝ-zero-from-sine-zero point sine-zero =
      tanℝ-definingEquation point
    ∙ divideOnTangentDomainPresNumerator
        point (sinℝ (fst point)) 0ℝ sine-zero
    ∙ divideZeroOnTangentDomain point


  secℝ-one-from-cosine-one : ∀ point →
    cosℝ (fst point) ≡ 1ℝ → secℝ point ≡ 1ℝ
  secℝ-one-from-cosine-one point cosine-one =
      secℝ-definingEquation point
    ∙ divideOnTangentDomainPresNumerator
        point 1ℝ (1ℝ · cosℝ (fst point))
        (sym
          (cong (1ℝ ·_) cosine-one
          ∙ mulIdL 1ℝ))
    ∙ divideMulRight
        1ℝ (cosℝ (fst point)) (snd point)
