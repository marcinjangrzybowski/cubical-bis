module Cubical.Analysis.Real.Calculus.Derivative.Polynomial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.List using (List; []; _∷_; map)
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Polynomial
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Basic
open import Cubical.Analysis.Real.Calculus.Derivative.Algebra
open import Cubical.Analysis.Real.Calculus.Derivative.Product
open import Cubical.Analysis.Real.Calculus.Derivative.Chain

open CategoryStructures


-- This is the formal derivative of the Horner evaluator.  It deliberately
-- follows the same recursion instead of first converting to a sum of
-- monomials: D(a + x * p) = p + x * D(p).
evaluatePolynomialDerivative : List ℝ → ℝ → ℝ
evaluatePolynomialDerivative [] x = 0ℝ
evaluatePolynomialDerivative (a ∷ coefficients) x =
  evaluatePolynomial coefficients x
    + x · evaluatePolynomialDerivative coefficients x


evaluatePolynomialDerivativeℚ : List ℚ → ℚ → ℚ
evaluatePolynomialDerivativeℚ [] x = 0
evaluatePolynomialDerivativeℚ (a ∷ coefficients) x =
  evaluatePolynomialℚ coefficients x
    ℚ.+ x ℚ.· evaluatePolynomialDerivativeℚ coefficients x


evaluatePolynomialDerivative-rat : ∀ coefficients x →
  evaluatePolynomialDerivative
      (map rat coefficients) (rat x)
    ≡
  rat (evaluatePolynomialDerivativeℚ coefficients x)
evaluatePolynomialDerivative-rat [] x = refl
evaluatePolynomialDerivative-rat (a ∷ coefficients) x =
  cong₂ _+_
    (evaluatePolynomial-rat coefficients x)
    ( cong (rat x ·_)
        (evaluatePolynomialDerivative-rat coefficients x)
    ∙ mul-rat x
        (evaluatePolynomialDerivativeℚ coefficients x)
    )
  ∙ rat+rat
      (evaluatePolynomialℚ coefficients x)
      (x ℚ.· evaluatePolynomialDerivativeℚ coefficients x)


evaluatePolynomialHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate : A → ℝ) →
  isContinuous source coordinate (ℝPremetricSpace .snd) →
  ∀ coefficients →
  IsDerivativeAlong
    source coordinate
    (λ point →
      evaluatePolynomial coefficients (coordinate point))
    (λ point →
      evaluatePolynomialDerivative coefficients
        (coordinate point))
evaluatePolynomialHasDerivativeAlong
    source coordinate coordinate-continuous [] =
  constantHasDerivativeAlong source coordinate 0ℝ
evaluatePolynomialHasDerivativeAlong
    {A = A} source coordinate coordinate-continuous
    (a ∷ coefficients) =
  subst
    (IsDerivativeAlong source coordinate function)
    derivativePath
    rawDerivative
  where
  tail : A → ℝ
  tail point =
    evaluatePolynomial coefficients (coordinate point)

  tailDerivative : A → ℝ
  tailDerivative point =
    evaluatePolynomialDerivative coefficients
      (coordinate point)

  product : A → ℝ
  product point = coordinate point · tail point

  productDerivative : A → ℝ
  productDerivative point =
    1ℝ · tail point + coordinate point · tailDerivative point

  function : A → ℝ
  function point = a + product point

  tailHasDerivative :
    IsDerivativeAlong
      source coordinate tail tailDerivative
  tailHasDerivative =
    evaluatePolynomialHasDerivativeAlong
      source coordinate coordinate-continuous coefficients

  productHasDerivative :
    IsDerivativeAlong
      source coordinate product productDerivative
  productHasDerivative =
    mulHasDerivativeAlong
      source coordinate
      coordinate tail
      (λ _ → 1ℝ) tailDerivative
      coordinate-continuous
      (coordinateHasDerivativeAlong source coordinate)
      tailHasDerivative

  rawDerivative :
    IsDerivativeAlong
      source coordinate function
      (λ point → 0ℝ + productDerivative point)
  rawDerivative =
    addHasDerivativeAlong
      source coordinate
      (λ _ → a) product
      (λ _ → 0ℝ) productDerivative
      (constantHasDerivativeAlong source coordinate a)
      productHasDerivative

  derivativePath :
    (λ point → 0ℝ + productDerivative point) ≡
    (λ point →
      evaluatePolynomialDerivative
        (a ∷ coefficients) (coordinate point))
  derivativePath =
    funExt λ point →
      addIdL (productDerivative point)
      ∙ cong
          (_+ coordinate point · tailDerivative point)
          (mulIdL (tail point))


evaluatePolynomialHasDerivative : ∀ coefficients →
  IsDerivative
    (evaluatePolynomial coefficients)
    (evaluatePolynomialDerivative coefficients)
evaluatePolynomialHasDerivative coefficients =
  evaluatePolynomialHasDerivativeAlong
    (ℝPremetricSpace .snd)
    (idfun ℝ)
    (snd (NE→C (idⁿ {M = ℝPremetricSpace})))
    coefficients


evaluatePolynomialCompositionHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → ℝ) →
  isContinuous source coordinate (ℝPremetricSpace .snd) →
  IsDerivativeAlong source coordinate function derivative →
  ∀ coefficients →
  IsDerivativeAlong
    source coordinate
    (λ point →
      evaluatePolynomial coefficients (function point))
    (λ point →
      evaluatePolynomialDerivative coefficients (function point)
        · derivative point)
evaluatePolynomialCompositionHasDerivativeAlong
    source coordinate function derivative
    coordinate-continuous function-derivative coefficients =
  chainHasDerivativeAlong
    source coordinate function derivative
    (evaluatePolynomial coefficients)
    (evaluatePolynomialDerivative coefficients)
    coordinate-continuous function-derivative
    (evaluatePolynomialHasDerivative coefficients)


evaluatePolynomialCompositionHasDerivative :
  ∀ function derivative →
  IsDerivative function derivative →
  ∀ coefficients →
  IsDerivative
    (λ x → evaluatePolynomial coefficients (function x))
    (λ x →
      evaluatePolynomialDerivative coefficients (function x)
        · derivative x)
evaluatePolynomialCompositionHasDerivative
    function derivative function-derivative coefficients =
  chainHasDerivative
    function derivative
    (evaluatePolynomial coefficients)
    (evaluatePolynomialDerivative coefficients)
    function-derivative
    (evaluatePolynomialHasDerivative coefficients)
