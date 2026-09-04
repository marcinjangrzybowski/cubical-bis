module Cubical.Analysis.Real.Series.PowerSeries.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Data.Nat using (ℕ; suc)
import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Algebra.Scalar.Compatibility
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Algebra
open import Cubical.Analysis.Real.Calculus.Derivative.Power


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


-- Shift the coefficients once and weight the new nth coefficient by n + 1.
formalDerivative : RealSequence → RealSequence
formalDerivative coefficients n =
  realNatural (suc n) · coefficients (suc n)


formalDerivative-add : ∀ a b →
  formalDerivative (λ n → a n + b n)
    ≡
  (λ n → formalDerivative a n + formalDerivative b n)
formalDerivative-add a b =
  funExt
    (λ n →
      mulDistR
        (realNatural (suc n))
        (a (suc n)) (b (suc n)))


formalDerivative-scale : ∀ c coefficients →
  formalDerivative (scaleSeries c coefficients)
    ≡
  scaleSeries c (formalDerivative coefficients)
formalDerivative-scale c coefficients =
  funExt
    (λ n →
      mulAssoc
        (realNatural (suc n)) c (coefficients (suc n))
      ∙ cong
          (_· coefficients (suc n))
          (mulComm (realNatural (suc n)) c)
      ∙ sym
          (mulAssoc
            c (realNatural (suc n)) (coefficients (suc n))))


formalDerivative-neg : ∀ coefficients →
  formalDerivative (λ n → - coefficients n)
    ≡ (λ n → - formalDerivative coefficients n)
formalDerivative-neg coefficients =
  funExt
    (λ n →
      ℝRing.-DistR·
        (realNatural (suc n)) (coefficients (suc n)))


formalDerivative-rationalScale : ∀ c coefficients →
  formalDerivative (λ n → c ⋆ coefficients n)
    ≡
  (λ n → c ⋆ formalDerivative coefficients n)
formalDerivative-rationalScale c coefficients =
  cong formalDerivative
    (funExt (λ n → scalar-as-mul c (coefficients n)))
  ∙ formalDerivative-scale (rat c) coefficients
  ∙ funExt
      (λ n → sym (scalar-as-mul c (formalDerivative coefficients n)))


formalDerivative-zero :
  formalDerivative (λ _ → 0ℝ) ≡ (λ _ → 0ℝ)
formalDerivative-zero =
  funExt
    (λ n → ℝRing.0RightAnnihilates (realNatural (suc n)))


formalDerivative-rat : ∀ (coefficients : ℕ → ℚ.ℚ) n →
  formalDerivative (λ k → rat (coefficients k)) n
    ≡
  rat (ℚ.fromNat (suc n) ℚ.· coefficients (suc n))
formalDerivative-rat coefficients n =
  mul-rat (ℚ.fromNat (suc n)) (coefficients (suc n))


powerSeriesTerms-formalDerivative : ∀ coefficients x n →
  powerSeriesTerms (formalDerivative coefficients) x n
    ≡
  realNatural (suc n) ·
    (coefficients (suc n) · powℝ x n)
powerSeriesTerms-formalDerivative coefficients x n =
  sym
    (mulAssoc
      (realNatural (suc n))
      (coefficients (suc n)) (powℝ x n))


powerSeriesTerms-formalDerivative-naturalPower :
  ∀ coefficients x n →
  powerSeriesTerms (formalDerivative coefficients) x n
    ≡
  coefficients (suc n) · naturalPowerDerivative (suc n) x
powerSeriesTerms-formalDerivative-naturalPower coefficients x n =
  cong
    (_· powℝ x n)
    (mulComm
      (realNatural (suc n)) (coefficients (suc n)))
  ∙ sym
      (mulAssoc
        (coefficients (suc n))
        (realNatural (suc n)) (powℝ x n))


powerSeriesSuccessorTermHasDerivative : ∀ coefficients n →
  IsDerivative
    (λ x → powerSeriesTerms coefficients x (suc n))
    (λ x → powerSeriesTerms (formalDerivative coefficients) x n)
powerSeriesSuccessorTermHasDerivative coefficients n =
  subst
    (IsDerivative
      (λ x → powerSeriesTerms coefficients x (suc n)))
    (funExt
      (λ x →
        sym
          (powerSeriesTerms-formalDerivative-naturalPower
            coefficients x n)))
    (scaleHasDerivative
      (λ x → powℝ x (suc n))
      (naturalPowerDerivative (suc n))
      (coefficients (suc n))
      (naturalPowerHasDerivative (suc n)))


powerSeriesTerms-formalDerivative-rat :
  ∀ (coefficients : ℕ → ℚ.ℚ) q n →
  powerSeriesTerms
      (formalDerivative (λ k → rat (coefficients k)))
      (rat q) n
    ≡
  rat
    ((ℚ.fromNat (suc n) ℚ.· coefficients (suc n))
      ℚ.· powℚ q n)
powerSeriesTerms-formalDerivative-rat coefficients q n =
  cong₂ _·_
    (formalDerivative-rat coefficients n)
    (pow-rat q n)
  ∙ mul-rat
      (ℚ.fromNat (suc n) ℚ.· coefficients (suc n))
      (powℚ q n)
