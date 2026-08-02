module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Derivative where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (suc)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Operations
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Majorant

formalDerivative :
  RealSequence → RealSequence
formalDerivative coefficients n =
  realNatural (suc n)
    · coefficients (suc n)

formalDerivative-add :
  ∀ a b →
  formalDerivative
      (λ n → a n + b n)
    ≡
  (λ n →
    formalDerivative a n
      + formalDerivative b n)
formalDerivative-add a b =
  funExt
    (λ n →
      mulDistR
        (realNatural (suc n))
        (a (suc n))
        (b (suc n)))

formalDerivative-scale :
  ∀ c coefficients →
  formalDerivative
      (scaleSeries c coefficients)
    ≡
  scaleSeries c
    (formalDerivative coefficients)
formalDerivative-scale c coefficients =
  funExt
    (λ n →
      sym
        (mulAssoc
          (realNatural (suc n))
          c
          (coefficients (suc n)))
      ∙ cong
          (_· coefficients (suc n))
          (mulComm
            (realNatural (suc n))
            c)
      ∙ mulAssoc
          c
          (realNatural (suc n))
          (coefficients (suc n)))

formalDerivative-zero :
  formalDerivative (λ _ → 0)
    ≡
  (λ _ → 0)
formalDerivative-zero =
  funExt
    (λ n →
      mulZeroR
        (realNatural (suc n)))

powerSeriesTerms-formalDerivative :
  ∀ coefficients x n →
  powerSeriesTerms
      (formalDerivative coefficients)
      x n
    ≡
  realNatural (suc n)
    · (coefficients (suc n)
      · x ^ⁿ n)
powerSeriesTerms-formalDerivative
  coefficients x n =
    mulAssoc
      (realNatural (suc n))
      (coefficients (suc n))
      (x ^ⁿ n)

formalDerivativeMajorant :
  RealSequence → RealSequence
formalDerivativeMajorant majorant n =
  realNatural (suc n)
    · majorant (suc n)

formalDerivativeMajorant-nonnegative :
  ∀ majorant →
  NonnegativeCoefficients majorant →
  NonnegativeCoefficients
    (formalDerivativeMajorant majorant)
formalDerivativeMajorant-nonnegative
  majorant nonnegative n =
    mulNonnegative
      (realNatural (suc n))
      (majorant (suc n))
      (realNatural-nonnegative
        (suc n))
      (nonnegative (suc n))

formalDerivativePresCoefficientMajorant :
  ∀ coefficients majorant →
  CoefficientMajorizedBy
    coefficients majorant →
  CoefficientMajorizedBy
    (formalDerivative coefficients)
    (formalDerivativeMajorant majorant)
formalDerivativePresCoefficientMajorant
  coefficients majorant majorized n =
    subst
      (_≤ℝ
        formalDerivativeMajorant majorant n)
      (sym absolute-path)
      (mulMono≤
        (realNatural (suc n))
        (realNatural (suc n))
        (absℝ (coefficients (suc n)))
        (majorant (suc n))
        (realNatural-nonnegative
          (suc n))
        (absNonnegative
          (coefficients (suc n)))
        (≤ℝ-refl
          (realNatural (suc n)))
        (majorized (suc n)))
  where
  absolute-path :
    absℝ
      (formalDerivative coefficients n)
      ≡
    realNatural (suc n)
      · absℝ (coefficients (suc n))
  absolute-path =
    absMul
      (realNatural (suc n))
      (coefficients (suc n))
    ∙ cong
        (_· absℝ (coefficients (suc n)))
        (absOfNonnegative
          (realNatural (suc n))
          (realNatural-nonnegative
            (suc n)))
