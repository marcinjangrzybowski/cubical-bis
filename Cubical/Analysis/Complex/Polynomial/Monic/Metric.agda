module Cubical.Analysis.Complex.Polynomial.Monic.Metric where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.FinData as Fin using (Fin; zero; suc)
open import Cubical.Data.Vec using (lookup; []; _∷_)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊; /2₊<id)
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Polynomial.Monic

private module C = PremetricStr (ℂPremetricSpace .snd)

CoefficientCloseness : ∀ {n} → MonicPolynomial n → ℚ₊ → MonicPolynomial n → Type₀
CoefficientCloseness {n} p ε q = ∀ (k : Fin n) → lookup k p ∼ℂ[ ε ] lookup k q

coefficientCloseness-monotone : ∀ {n} (p q : MonicPolynomial n) δ ε → δ ≤₊ ε →
  CoefficientCloseness p δ q → CoefficientCloseness p ε q
coefficientCloseness-monotone p q δ ε below close k = C.isMonotone≈≤ (lookup k p) (lookup k q) δ ε below (close k)

coefficientCloseness-halfTriangle : ∀ {n} (p q r : MonicPolynomial n) ε →
  CoefficientCloseness p (ε /2₊) q → CoefficientCloseness q (ε /2₊) r → CoefficientCloseness p ε r
coefficientCloseness-halfTriangle p q r ε pq qr k = C.subst≈ _ _ (1/2∈ℚ./2+/2≡id (fst ε))
  (C.isTriangular≈ (lookup k p) (lookup k q) (lookup k r) (ε /2₊) (ε /2₊) (pq k) (qr k))

addConstant-halfCloseness : ∀ {n} a b (p q : MonicPolynomial (suc n)) ε →
  a ∼ℂ[ ε /2₊ ] b → CoefficientCloseness p (ε /2₊) q →
  CoefficientCloseness (addConstant a p) ε (addConstant b q)
addConstant-halfCloseness a b (c ∷ p) (d ∷ q) ε ab pq zero = addℂ-presHalfCloseness a b c d ε ab (pq zero)
addConstant-halfCloseness a b (c ∷ p) (d ∷ q) ε ab pq (suc k) =
  C.isMonotone≈< (lookup k p) (lookup k q) (ε /2₊) ε (/2₊<id ε) (pq (suc k))

addConstant-small : ∀ {n} a (p : MonicPolynomial (suc n)) ε → a ∼ℂ[ ε ] 0ℂ →
  CoefficientCloseness (addConstant a p) ε p
addConstant-small a (b ∷ p) ε small zero = subst ((a +ℂ b) ∼ℂ[ ε ]_)
  (+ℂComm 0ℂ b ∙ +ℂIdR b) (addℂ-presClosenessR b a 0ℂ ε small)
addConstant-small a (b ∷ p) ε small (suc k) = refl∼ℂ (lookup k p) ε
