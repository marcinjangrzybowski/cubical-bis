module Cubical.Analysis.Complex.Polynomial.Formal where

-- Interpret finite coefficient lists in the existing polynomial ring.
-- This justifies ring calculations on zero-extended coefficient identities,
-- including lists with trailing zeros. No evaluation-extensionality or
-- decidable equality on the coefficient ring is assumed.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
import Cubical.Data.Vec as V
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Polynomials.UnivariateList.Base as PB
import Cubical.Algebra.Polynomials.UnivariateList.Properties as PP
open import Cubical.Algebra.CommRing.Polynomials.UnivariatePolyList
import Cubical.Analysis.Complex.Polynomial.Algebra as Polynomials
import Cubical.Analysis.Complex.Polynomial.MonicAlgebra as Monic
import Cubical.Analysis.Complex.Polynomial.Differential.Algebra as Differential
import Cubical.Analysis.Complex.Polynomial.Differential.MonicAlgebra as MonicDifferential
import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.PolynomialAlgebra as Certificates

module Formal {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open Polynomials.Polynomials R
  open Monic.Monic R
  open Differential.Differential R
  open MonicDifferential.MonicDifferential R
  open Certificates.Certificates R
  private
    A = fst R
    module P = PB.PolyMod R
    module Q = PP.PolyModTheory R

  polynomialRing : CommRing ℓ
  polynomialRing = UnivariatePolyList R

  private
    module S = CommRingStr (snd polynomialRing)
    module MP = Monic.Monic polynomialRing
    module DP = MonicDifferential.MonicDifferential polynomialRing
    module C = IsCommRingHom (snd (constantPolynomialHom R))

  constant : A → PB.Poly R
  constant a = a PB.∷ PB.[]

  variablePolynomial : PB.Poly R
  variablePolynomial = 0r PB.∷ 1r PB.∷ PB.[]

  encode : List A → PB.Poly R
  encode [] = PB.[]
  encode (a ∷ p) = a PB.∷ encode p

  encode-coefficient : ∀ p k → P.Poly→Fun (encode p) k ≡ coefficient p k
  encode-coefficient [] k = refl
  encode-coefficient (a ∷ p) zero = refl
  encode-coefficient (a ∷ p) (suc k) = encode-coefficient p k

  encode-identity : ∀ p q → PolynomialIdentity p q → encode p ≡ encode q
  encode-identity p q equal = P.polyEq (encode p) (encode q)
    (funExt λ k → encode-coefficient p k ∙ equal k ∙ sym (encode-coefficient q k))

  decode-identity : ∀ p q → encode p ≡ encode q → PolynomialIdentity p q
  decode-identity p q equal k = sym (encode-coefficient p k)
    ∙ cong (λ v → P.Poly→Fun v k) equal ∙ encode-coefficient q k

  encode-add : ∀ p q → encode (addCoefficients p q) ≡ encode p S.+ encode q
  encode-add [] q = sym (Q.Poly+Lid (encode q))
  encode-add (a ∷ p) [] = refl
  encode-add (a ∷ p) (b ∷ q) = cong ((a + b) PB.∷_) (encode-add p q)

  private
    encode-scale : ∀ a p → encode (scaleCoefficients a p) ≡ a Q.PolyConst* encode p
    encode-scale a [] = refl
    encode-scale a (b ∷ p) = cong ((a · b) PB.∷_) (encode-scale a p)

  encode-multiply : ∀ p q → encode (multiplyCoefficients p q) ≡ encode p S.· encode q
  encode-multiply [] q = refl
  encode-multiply (a ∷ p) q = encode-add (scaleCoefficients a q) (0r ∷ multiplyCoefficients p q)
    ∙ cong₂ S._+_ (encode-scale a q) (cong (0r PB.∷_) (encode-multiply p q))

  private
    horner : ∀ a q → a PB.∷ q ≡ constant a S.+ (variablePolynomial S.· q)
    horner a q = sym (cong (constant a S.+_) (Q.X*Poly q)
      ∙ cong₂ PB._∷_ (+IdR a) (Q.Poly+Lid q))

  monicValue : ∀ {n} → MonicPolynomial n → PB.Poly R
  monicValue p = MP.evaluateMonic (V.map constant p) variablePolynomial

  monicDerivative : ∀ {n} → MonicPolynomial n → PB.Poly R
  monicDerivative p = DP.derivativeMonic (V.map constant p) variablePolynomial

  encode-monic : ∀ {n} (p : MonicPolynomial n) → encode (monicCoefficients p) ≡ monicValue p
  encode-monic V.[] = refl
  encode-monic (a V.∷ p) = horner a (encode (monicCoefficients p))
    ∙ cong (λ q → constant a S.+ (variablePolynomial S.· q)) (encode-monic p)

  encode-derivative : ∀ {n} (p : MonicPolynomial n) →
    encode (differentiate (monicCoefficients p)) ≡ monicDerivative p
  encode-derivative V.[] = PB.drop0
  encode-derivative (a V.∷ p) = encode-add (monicCoefficients p) (0r ∷ differentiate (monicCoefficients p))
    ∙ cong₂ S._+_ (encode-monic p)
      (sym (Q.X*Poly (encode (differentiate (monicCoefficients p))))
        ∙ cong (variablePolynomial S.·_) (encode-derivative p))

  private
    map-addConstant : ∀ {n} a (p : MonicPolynomial (suc n)) →
      V.map constant (addConstant a p) ≡ MP.addConstant (constant a) (V.map constant p)
    map-addConstant a (b V.∷ p) = cong (V._∷ V.map constant p) (C.pres+ a b)

    map-multiplyLinear : ∀ {n} r (p : MonicPolynomial n) →
      V.map constant (multiplyLinear r p) ≡ MP.multiplyLinear (constant r) (V.map constant p)
    map-multiplyLinear r V.[] = cong (V._∷ V.[]) (C.pres- r)
    map-multiplyLinear r (a V.∷ p) = cong₂ V._∷_
      (C.pres· (- r) a ∙ cong (S._· constant a) (C.pres- r))
      (map-addConstant a (multiplyLinear r p)
        ∙ cong (MP.addConstant (constant a)) (map-multiplyLinear r p))

  monicValue-multiplyLinear : ∀ {n} r (p : MonicPolynomial n) →
    monicValue (multiplyLinear r p) ≡ (variablePolynomial S.- constant r) S.· monicValue p
  monicValue-multiplyLinear r p = cong (λ q → MP.evaluateMonic q variablePolynomial) (map-multiplyLinear r p)
    ∙ MP.evaluate-multiplyLinear (constant r) (V.map constant p) variablePolynomial

  monicDerivative-multiplyLinear : ∀ {n} r (p : MonicPolynomial n) →
    monicDerivative (multiplyLinear r p) ≡ monicValue p S.+
      ((variablePolynomial S.- constant r) S.· monicDerivative p)
  monicDerivative-multiplyLinear r p =
    cong (λ q → DP.derivativeMonic q variablePolynomial) (map-multiplyLinear r p)
    ∙ DP.derivative-multiplyLinear (constant r) (V.map constant p) variablePolynomial

  encode-linear : ∀ r → encode ((- r) ∷ 1r ∷ []) ≡ variablePolynomial S.- constant r
  encode-linear r = encode-monic (multiplyLinear r V.[])
    ∙ monicValue-multiplyLinear r V.[] ∙ S.·IdR (variablePolynomial S.- constant r)
