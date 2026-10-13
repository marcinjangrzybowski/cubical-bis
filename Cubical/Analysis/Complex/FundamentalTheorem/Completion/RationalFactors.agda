module Cubical.Analysis.Complex.FundamentalTheorem.Completion.RationalFactors where

-- On Gaussian-rational coefficients, finite factor approximation has a
-- decidable test. Search of the explicit enumeration therefore constructs
-- a deterministic approximation at every requested accuracy.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (zero; suc; ∀Dec)
import Cubical.Data.Sum as Sum
open import Cubical.Data.Vec using (Vec; []; _∷_; map; lookup)
open import Cubical.Data.Sigma
import Cubical.Data.Rationals.Base as Q
import Cubical.Data.Rationals.Properties as Q
import Cubical.Data.Rationals.Order as Q
import Cubical.Data.Rationals.Order.AbsoluteValue as Q
open import Cubical.Relation.Nullary using (Dec; yes; no; mapDec; Dec×)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing.Instances.Rationals using (ℚCommRing)
open import Cubical.Algebra.OrderedCommRing using (module OrderedCommRingTheory)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base using (rat-rat; rat-rat-reflects)
import Cubical.Analysis.Real.Algebra.Addition as Add
import Cubical.Analysis.Real.Algebra.Negation as Neg
import Cubical.Analysis.Real.Algebra.Multiplication as Mul
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
import Cubical.Analysis.Complex.Algebra.Cartesian as Cartesian
import Cubical.Analysis.Complex.Polynomial.MonicAlgebra as Monic
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Presented
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Coefficients
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Gaussian using (lookup-gaussian)
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Density
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Enumeration
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.FiniteSearch

module G = Cartesian.Cartesian ℚCommRing
module GM = Monic.Monic G.pairCommRing
private module QR = OrderedCommRingTheory ℚOrderedCommRing

opaque
  gaussian-add : ∀ a b → gaussianℂ (a G.+ℂ b) ≡ gaussianℂ a +ℂ gaussianℂ b
  gaussian-add (a , b) (c , d) = sym (cong₂ _,_ (Add.rat+rat a c) (Add.rat+rat b d))

  gaussian-neg : ∀ a → gaussianℂ (G.-ℂ a) ≡ -ℂ gaussianℂ a
  gaussian-neg (a , b) = sym (cong₂ _,_ (Neg.neg-rat a) (Neg.neg-rat b))

  gaussian-mul : ∀ a b → gaussianℂ (a G.·ℂ b) ≡ gaussianℂ a ·ℂ gaussianℂ b
  gaussian-mul (a , b) (c , d) = sym (cong₂ _,_
    (cong₂ Add._+_ (Mul.mul-rat a c)
      (cong Neg.-_ (Mul.mul-rat b d) ∙ Neg.neg-rat (b Q.· d))
      ∙ Add.rat+rat (a Q.· c) (Q.- (b Q.· d)))
    (cong₂ Add._+_ (Mul.mul-rat a d) (Mul.mul-rat b c) ∙ Add.rat+rat (a Q.· d) (b Q.· c)))

  gaussian-addConstant : ∀ {n} a (p : Vec GaussianRational (suc n)) →
    map gaussianℂ (GM.addConstant a p) ≡ addConstant (gaussianℂ a) (map gaussianℂ p)
  gaussian-addConstant a (b ∷ p) = cong (_∷ map gaussianℂ p) (gaussian-add a b)

  gaussian-multiplyLinear : ∀ {n} r (p : Vec GaussianRational n) →
    map gaussianℂ (GM.multiplyLinear r p) ≡ multiplyLinear (gaussianℂ r) (map gaussianℂ p)
  gaussian-multiplyLinear r [] = cong (_∷ []) (gaussian-neg r)
  gaussian-multiplyLinear r (a ∷ p) = cong₂ _∷_
    (gaussian-mul (G.-ℂ r) a ∙ cong (_·ℂ gaussianℂ a) (gaussian-neg r))
    (gaussian-addConstant a (GM.multiplyLinear r p)
      ∙ cong (addConstant (gaussianℂ a)) (gaussian-multiplyLinear r p))

  gaussian-linearFactors : ∀ {n} (qs : Vec GaussianRational n) →
    map gaussianℂ (GM.linearFactors qs) ≡ gaussianFactors qs
  gaussian-linearFactors [] = refl
  gaussian-linearFactors (q ∷ qs) = gaussian-multiplyLinear q (GM.linearFactors qs)
    ∙ cong (multiplyLinear (gaussianℂ q)) (gaussian-linearFactors qs)

  gaussian-close-dec : ∀ a b ε → Dec (gaussianℂ a ∼ℂ[ ε ] gaussianℂ b)
  gaussian-close-dec (a , b) (c , d) ε = Dec×
    (mapDec (rat-rat a c ε) (λ absent close → absent (rat-rat-reflects a c ε close))
      (Q.<Dec (QR.abs (a Q.- c)) (fst ε)))
    (mapDec (rat-rat b d ε) (λ absent close → absent (rat-rat-reflects b d ε close))
      (Q.<Dec (QR.abs (b Q.- d)) (fst ε)))

  gaussian-coefficients-dec : ∀ {n} (p q : Vec GaussianRational n) ε →
    Dec (CoefficientCloseness (map gaussianℂ p) ε (map gaussianℂ q))
  gaussian-coefficients-dec p q ε = Sum.rec yes
    (λ { (i , absent) → no (λ close → absent (close i)) })
    (∀Dec _ (λ i → subst2 (λ a b → Dec (a ∼ℂ[ ε ] b))
      (sym (lookup-gaussian p i)) (sym (lookup-gaussian q i))
      (gaussian-close-dec (lookup i p) (lookup i q) ε)))

  rational-factor-test : ∀ {n} (p qs : Vec GaussianRational n) ε →
    Dec (CoefficientCloseness (map gaussianℂ p) ε (gaussianFactors qs))
  rational-factor-test p qs ε = subst (λ q → Dec (CoefficientCloseness (map gaussianℂ p) ε q))
    (gaussian-linearFactors qs) (gaussian-coefficients-dec p (GM.linearFactors qs) ε)

  chosenRationalFactors : ∀ {n} (p : Vec GaussianRational n) ε →
    Σ[ qs ∈ Vec GaussianRational n ] CoefficientCloseness (map gaussianℂ p) ε (gaussianFactors qs)
  chosenRationalFactors {n} p ε = configurationEnumeration n (fst selected) , snd selected
    where
    Test : ℕ → Type₀
    Test k = CoefficientCloseness (map gaussianℂ p) ε (gaussianFactors (configurationEnumeration n k))

    inhabited : PT.∥ Σ[ k ∈ ℕ ] Test k ∥₁
    inhabited = PT.rec PT.isPropPropTrunc
      (λ { (qs , close) → PT.map
        (λ { (k , equal) → k , subst (λ rs → CoefficientCloseness (map gaussianℂ p) ε (gaussianFactors rs))
          (sym equal) close }) (configurationEnumeration-surjective qs) })
      (gaussian-factor-density n (map gaussianℂ p) ε)

    selected : Σ[ k ∈ ℕ ] Test k
    selected = firstWitness Test
      (λ k → coefficientCloseness-prop (map gaussianℂ p) (gaussianFactors (configurationEnumeration n k)) ε)
      (λ k → rational-factor-test p (configurationEnumeration n k) ε) inhabited
