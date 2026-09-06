module Cubical.Analysis.Real.Algebra.Polynomial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.List using (List; []; _∷_; map)
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Mappings
  using (constantRealMapIsContinuous)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Sequence using
  (isLimitSequence; continuousPreservesIsLimitSequence)

open CategoryStructures


-- Coefficients are stored in increasing degree order.  Horner evaluation
-- keeps both the definition and its continuity proof compositional.

evaluatePolynomial : List ℝ → ℝ → ℝ
evaluatePolynomial [] x = 0ℝ
evaluatePolynomial (a ∷ coefficients) x =
  a + x · evaluatePolynomial coefficients x


evaluatePolynomialℚ : List ℚ → ℚ → ℚ
evaluatePolynomialℚ [] x = 0
evaluatePolynomialℚ (a ∷ coefficients) x =
  a ℚ.+ x ℚ.· evaluatePolynomialℚ coefficients x


evaluatePolynomial-rat : ∀ coefficients x →
  evaluatePolynomial (map rat coefficients) (rat x) ≡
  rat (evaluatePolynomialℚ coefficients x)
evaluatePolynomial-rat [] x = refl
evaluatePolynomial-rat (a ∷ coefficients) x =
  cong
    (λ tail → rat a + rat x · tail)
    (evaluatePolynomial-rat coefficients x)
  ∙ cong (rat a +_)
      (mul-rat x (evaluatePolynomialℚ coefficients x))
  ∙ rat+rat
      a (x ℚ.· evaluatePolynomialℚ coefficients x)


private
  constant-isContinuous :
    ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A) (a : ℝ) →
    isContinuous source (λ (_ : A) → a)
      (ℝPremetricSpace .snd)
  constant-isContinuous = constantRealMapIsContinuous


evaluatePolynomialOfContinuousIsContinuous :
  ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A)
  (x : A → ℝ) →
  isContinuous source x (ℝPremetricSpace .snd) →
  ∀ coefficients →
  isContinuous source
    (λ point → evaluatePolynomial coefficients (x point))
    (ℝPremetricSpace .snd)
evaluatePolynomialOfContinuousIsContinuous
  source x x-continuous [] =
  constant-isContinuous source 0ℝ
evaluatePolynomialOfContinuousIsContinuous
  source x x-continuous (a ∷ coefficients) =
  addOfContinuousIsContinuous
    source
    (λ _ → a)
    (λ point →
      x point · evaluatePolynomial coefficients (x point))
    (constant-isContinuous source a)
    (mulOfContinuousIsContinuous
      source
      x
      (λ point → evaluatePolynomial coefficients (x point))
      x-continuous
      (evaluatePolynomialOfContinuousIsContinuous
        source x x-continuous coefficients))


evaluatePolynomialIsContinuous : ∀ coefficients →
  isContinuous
    (ℝPremetricSpace .snd)
    (evaluatePolynomial coefficients)
    (ℝPremetricSpace .snd)
evaluatePolynomialIsContinuous coefficients =
  evaluatePolynomialOfContinuousIsContinuous
    (ℝPremetricSpace .snd)
    (idfun ℝ)
    (snd (NE→C (idⁿ {M = ℝPremetricSpace})))
    coefficients


evaluatePolynomialPresIsLimitSequence : ∀ coefficients {x l} →
  isLimitSequence x l →
  isLimitSequence
    (evaluatePolynomial coefficients ∘ x)
    (evaluatePolynomial coefficients l)
evaluatePolynomialPresIsLimitSequence coefficients =
  continuousPreservesIsLimitSequence
    (evaluatePolynomial coefficients)
    (evaluatePolynomialIsContinuous coefficients)
