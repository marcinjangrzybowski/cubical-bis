module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric.Tangent.Addition where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Signed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.MultiplicativeApartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric.Tangent


private
  module TangentAdditionAlgebra {ℓ} (R : CommRing ℓ) where
    open CommRingStr (snd R)

    cosine-factor : ∀ sx sy cx cy tx ty →
      cx · tx ≡ sx → cy · ty ≡ sy →
      (cx · cy) - (sx · sy)
        ≡
      (cx · cy) · (1r - (tx · ty))
    cosine-factor sx sy cx cy tx ty x-law y-law =
        cong
          (λ value → (cx · cy) - value)
          (cong₂ _·_ (sym x-law) (sym y-law))
      ∙ solve! R

    sine-factor : ∀ sx sy cx cy tx ty →
      cx · tx ≡ sx → cy · ty ≡ sy →
      (sx · cy) + (cx · sy)
        ≡
      (cx · cy) · (tx + ty)
    sine-factor sx sy cx cy tx ty x-law y-law =
        cong₂ _+_
          (cong (_· cy) (sym x-law))
          (cong (cx ·_) (sym y-law))
      ∙ solve! R

    commute-common-factor : ∀ common tangent denominator →
      common · (tangent · denominator)
        ≡ tangent · (common · denominator)
    commute-common-factor common tangent denominator = solve! R


-- A pair of tangent-domain points can be added precisely when the cosine of
-- their sum is also apart from zero.  Keeping that third local gap in the
-- domain avoids pretending that tangent is closed under arbitrary addition.

TangentPair : Type₀
TangentPair = TangentDomain × TangentDomain


tangentPairSum : TangentPair → Real.ℝ
tangentPairSum points =
  fst (fst points) Add.+ fst (snd points)


TangentAdditionDomain : Type₀
TangentAdditionDomain =
  Σ[ points ∈ TangentPair ]
    Real.ιℚ 0 ＃ cosℝ (tangentPairSum points)


tangentAdditionLeft :
  TangentAdditionDomain → TangentDomain
tangentAdditionLeft addition-data = fst (fst addition-data)


tangentAdditionRight :
  TangentAdditionDomain → TangentDomain
tangentAdditionRight addition-data = snd (fst addition-data)


tangentAdditionSumPoint :
  TangentAdditionDomain → TangentDomain
tangentAdditionSumPoint addition-data =
  tangentPairSum (fst addition-data) , snd addition-data


tangentAdditionDenominator :
  TangentDomain → TangentDomain → Real.ℝ
tangentAdditionDenominator left right =
  Real.ιℚ 1 Group.- (tanℝ left Mul.· tanℝ right)


tangentAdditionNumerator :
  TangentDomain → TangentDomain → Real.ℝ
tangentAdditionNumerator left right =
  tanℝ left Add.+ tanℝ right


private
  commonCosineFactor :
    TangentDomain → TangentDomain → Real.ℝ
  commonCosineFactor left right =
    cosℝ (fst left) Mul.· cosℝ (fst right)


-- These two factorizations are the algebraic heart of the tangent addition
-- theorem.  They expose the common nonzero cosine factor before any division
-- occurs, which is what lets constructive apartness recover the new quotient
-- denominator below.

tangentAdditionCosineFactorization : ∀ left right →
  cosℝ (fst left Add.+ fst right)
    ≡
  commonCosineFactor left right Mul.·
    tangentAdditionDenominator left right
tangentAdditionCosineFactorization left right =
    cosℝ-add (fst left) (fst right)
  ∙ TangentAdditionAlgebra.cosine-factor ℝCommRing
      (sinℝ (fst left)) (sinℝ (fst right))
      (cosℝ (fst left)) (cosℝ (fst right))
      (tanℝ left) (tanℝ right)
      (cosℝ-mul-tanℝ left)
      (cosℝ-mul-tanℝ right)


tangentAdditionSineFactorization : ∀ left right →
  sinℝ (fst left Add.+ fst right)
    ≡
  commonCosineFactor left right Mul.·
    tangentAdditionNumerator left right
tangentAdditionSineFactorization left right =
    sinℝ-add (fst left) (fst right)
  ∙ TangentAdditionAlgebra.sine-factor ℝCommRing
      (sinℝ (fst left)) (sinℝ (fst right))
      (cosℝ (fst left)) (cosℝ (fst right))
      (tanℝ left) (tanℝ right)
      (cosℝ-mul-tanℝ left)
      (cosℝ-mul-tanℝ right)


tangentAdditionCommonFactorApart : ∀ left right →
  Real.ιℚ 0 ＃ commonCosineFactor left right
tangentAdditionCommonFactorApart left right =
  apartMul
    (cosℝ (fst left)) (cosℝ (fst right))
    (snd left) (snd right)


-- If x, y, and x+y lie in the tangent domain, then
-- 1 - tan(x)tan(y) is constructively apart from zero.  This is stronger than
-- merely assuming the denominator nonzero: its gap is derived by reflecting
-- apartness through the factored cosine addition law.

tangentAdditionDenominatorApart : ∀ addition-data →
  Real.ιℚ 0 ＃
    tangentAdditionDenominator
      (tangentAdditionLeft addition-data)
      (tangentAdditionRight addition-data)
tangentAdditionDenominatorApart addition-data =
  apartMul-reflects-right common denominator common-apart product-apart
  where
  left : TangentDomain
  left = tangentAdditionLeft addition-data

  right : TangentDomain
  right = tangentAdditionRight addition-data

  common : Real.ℝ
  common = commonCosineFactor left right

  denominator : Real.ℝ
  denominator = tangentAdditionDenominator left right

  common-apart : Real.ιℚ 0 ＃ common
  common-apart = tangentAdditionCommonFactorApart left right

  product-apart : Real.ιℚ 0 ＃ (common Mul.· denominator)
  product-apart =
    subst
      (Real.ιℚ 0 ＃_)
      (tangentAdditionCosineFactorization left right)
      (snd addition-data)


-- The division-free form remains useful to clients that only need to clear
-- denominators.  Its proof cancels the common cosine factor with the new
-- signed-inverse cancellation API.

tanℝ-add-cleared : ∀ addition-data →
  tanℝ (tangentAdditionSumPoint addition-data) Mul.·
      tangentAdditionDenominator
        (tangentAdditionLeft addition-data)
        (tangentAdditionRight addition-data)
    ≡
  tangentAdditionNumerator
    (tangentAdditionLeft addition-data)
    (tangentAdditionRight addition-data)
tanℝ-add-cleared addition-data =
  mul-cancel-left-apart
    tangent-times-denominator numerator common common-apart
    multiplied-equality
  where
  left : TangentDomain
  left = tangentAdditionLeft addition-data

  right : TangentDomain
  right = tangentAdditionRight addition-data

  sum-point : TangentDomain
  sum-point = tangentAdditionSumPoint addition-data

  common : Real.ℝ
  common = commonCosineFactor left right

  denominator : Real.ℝ
  denominator = tangentAdditionDenominator left right

  numerator : Real.ℝ
  numerator = tangentAdditionNumerator left right

  tangent-times-denominator : Real.ℝ
  tangent-times-denominator = tanℝ sum-point Mul.· denominator

  common-apart : Real.ιℚ 0 ＃ common
  common-apart = tangentAdditionCommonFactorApart left right

  multiplied-equality :
    common Mul.· tangent-times-denominator
      ≡ common Mul.· numerator
  multiplied-equality =
      TangentAdditionAlgebra.commute-common-factor ℝCommRing
        common (tanℝ sum-point) denominator
    ∙ cong
        (tanℝ sum-point Mul.·_)
        (sym (tangentAdditionCosineFactorization left right))
    ∙ tanℝ-mul-cosℝ sum-point
    ∙ tangentAdditionSineFactorization left right


tanℝ-add : ∀ addition-data →
  tanℝ (tangentAdditionSumPoint addition-data)
    ≡
  divideℝ
    (tangentAdditionNumerator
      (tangentAdditionLeft addition-data)
      (tangentAdditionRight addition-data))
    (tangentAdditionDenominator
      (tangentAdditionLeft addition-data)
      (tangentAdditionRight addition-data))
    (tangentAdditionDenominatorApart addition-data)
tanℝ-add addition-data =
  mul-cancel-right-apart
    (tanℝ sum-point)
    (divideℝ numerator denominator denominator-apart)
    denominator denominator-apart
    ( tanℝ-add-cleared addition-data
    ∙ sym (mulDivideRight numerator denominator denominator-apart))
  where
  sum-point : TangentDomain
  sum-point = tangentAdditionSumPoint addition-data

  numerator : Real.ℝ
  numerator =
    tangentAdditionNumerator
      (tangentAdditionLeft addition-data)
      (tangentAdditionRight addition-data)

  denominator : Real.ℝ
  denominator =
    tangentAdditionDenominator
      (tangentAdditionLeft addition-data)
      (tangentAdditionRight addition-data)

  denominator-apart : Real.ιℚ 0 ＃ denominator
  denominator-apart = tangentAdditionDenominatorApart addition-data
