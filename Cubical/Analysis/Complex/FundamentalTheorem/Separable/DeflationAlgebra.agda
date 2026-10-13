module Cubical.Analysis.Complex.FundamentalTheorem.Separable.DeflationAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Polynomial.Algebra as PolynomialDefinition
import Cubical.Analysis.Complex.Polynomial.MonicAlgebra as MonicDefinition
import Cubical.Analysis.Complex.Polynomial.Differential.Algebra as DifferentialDefinition
import Cubical.Analysis.Complex.Polynomial.Differential.MonicAlgebra as MonicDifferentialDefinition
import Cubical.Analysis.Complex.Polynomial.Formal as FormalDefinition
import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.PolynomialAlgebra as CertificatesDefinition

private module Rearrange {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  step : ∀ s t l q d → (s · l + t) · q + (t · l) · d ≡ s · (l · q) + t · (q + l · d)
  step s t l q d = solve! R

module Deflation {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open PolynomialDefinition.Polynomials R
  open MonicDefinition.Monic R
  open DifferentialDefinition.Differential R
  open MonicDifferentialDefinition.MonicDifferential R
  open CertificatesDefinition.Certificates R
  open FormalDefinition.Formal R
  private
    module S = CommRingStr (snd polynomialRing)
    module I = Rearrange polynomialRing

    expression : ∀ {n} (p : MonicPolynomial n) s t →
      encode (addCoefficients (multiplyCoefficients s (monicCoefficients p))
        (multiplyCoefficients t (differentiate (monicCoefficients p)))) ≡
      (encode s S.· monicValue p) S.+ (encode t S.· monicDerivative p)
    expression p s t = encode-add (multiplyCoefficients s (monicCoefficients p))
      (multiplyCoefficients t (differentiate (monicCoefficients p)))
      ∙ cong₂ S._+_
        (encode-multiply s (monicCoefficients p) ∙ cong (encode s S.·_) (encode-monic p))
        (encode-multiply t (differentiate (monicCoefficients p)) ∙ cong (encode t S.·_) (encode-derivative p))

  -- For p=(X-r)q and p' = q+(X-r)q', the new pair is
  -- s' = s(X-r)+t and t' = t(X-r). This is proved as a formal
  -- coefficient identity, not merely as equality at complex arguments.
  deflateCertificate : ∀ {n} (p : MonicPolynomial (suc n)) r →
    evaluateMonic p r ≡ 0r → BezoutSeparability p → BezoutSeparability (quotientMonic p r)
  deflateCertificate p r root certificate = record
    { bezoutS = s′
    ; bezoutT = t′
    ; bezoutIdentity = decode-identity
        (addCoefficients (multiplyCoefficients s′ (monicCoefficients q))
          (multiplyCoefficients t′ (differentiate (monicCoefficients q)))) (1r ∷ []) formalIdentity
    }
    where
    q = quotientMonic p r
    s = BezoutSeparability.bezoutS certificate
    t = BezoutSeparability.bezoutT certificate
    linear = (- r) ∷ 1r ∷ []
    s′ = addCoefficients (multiplyCoefficients s linear) t
    t′ = multiplyCoefficients t linear
    l = variablePolynomial S.- constant r

    oldIdentity : (encode s S.· monicValue p) S.+ (encode t S.· monicDerivative p) ≡ S.1r
    oldIdentity = sym (expression p s t)
      ∙ encode-identity
        (addCoefficients (multiplyCoefficients s (monicCoefficients p))
          (multiplyCoefficients t (differentiate (monicCoefficients p)))) (1r ∷ [])
        (BezoutSeparability.bezoutIdentity certificate)

    valueFactor : monicValue p ≡ l S.· monicValue q
    valueFactor = cong monicValue (factorMonicAtRoot p r root) ∙ monicValue-multiplyLinear r q

    derivativeFactor : monicDerivative p ≡ monicValue q S.+ (l S.· monicDerivative q)
    derivativeFactor = cong monicDerivative (factorMonicAtRoot p r root) ∙ monicDerivative-multiplyLinear r q

    formalIdentity : encode (addCoefficients (multiplyCoefficients s′ (monicCoefficients q))
      (multiplyCoefficients t′ (differentiate (monicCoefficients q)))) ≡ encode (1r ∷ [])
    formalIdentity = expression q s′ t′
      ∙ cong₂ (λ a b → (a S.· monicValue q) S.+ (b S.· monicDerivative q))
        (encode-add (multiplyCoefficients s linear) t
          ∙ cong (S._+ encode t) (encode-multiply s linear ∙ cong (encode s S.·_) (encode-linear r)))
        (encode-multiply t linear ∙ cong (encode t S.·_) (encode-linear r))
      ∙ I.step (encode s) (encode t) l (monicValue q) (monicDerivative q)
      ∙ cong₂ (λ v d → (encode s S.· v) S.+ (encode t S.· d)) (sym valueFactor) (sym derivativeFactor)
      ∙ oldIdentity
