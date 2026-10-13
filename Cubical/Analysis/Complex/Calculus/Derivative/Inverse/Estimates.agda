module Cubical.Analysis.Complex.Calculus.Derivative.Inverse.Estimates where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Inverse
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_; rat+rat)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (addComm)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (mulIdL; mulDistL)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition using (addReflects≤R)
open import Cubical.Analysis.Real.Order.AbsoluteValue using (addPres≤)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Estimates
import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Inverse.Algebra as Algebra

private
  module E = Algebra.InverseRemainder ℂCommRing

  opaque
    absorption : ∀ (h a k : ℝ) → k + k ≡ h → h ≤ℝ a + k → h ≤ℝ a + a
    absorption h a k double bound = subst (_≤ℝ a + a) double
      (addPres≤ k a k a halfBound halfBound)
      where
      halfBound : k ≤ℝ a
      halfBound = addReflects≤R k a k (subst (_≤ℝ a + k) (sym double) bound)

  opaque
    halfAbsorption : ∀ h a → h ≤ℝ a + rat (fst (1₊ /2₊)) · h → h ≤ℝ a + a
    halfAbsorption h a = absorption h a (rat (fst (1₊ /2₊)) · h)
      (halfErrorSum 1₊ h ∙ mulIdL h)

opaque
  inverseChordBound : ∀ inverse derivative → inverse ·ℂ derivative ≡ 1ℂ → ∀ x y u v C →
    normℂ inverse ≤ℝ rat (fst C) →
    normℂ ((y -ℂ x) -ℂ derivative ·ℂ (v -ℂ u)) ≤ℝ rat (fst ((1₊ /2₊) ₊／₊ C)) · normℂ (v -ℂ u) →
    normℂ (v -ℂ u) ≤ℝ rat (fst (C +₊ C)) · normℂ (y -ℂ x)
  inverseChordBound inverse derivative law x y u v C bounded small =
    subst (h ≤ℝ_) doubled (halfAbsorption h a absorbed)
    where
    h a : ℝ
    h = normℂ (v -ℂ u)
    a = rat (fst C) · normℂ (y -ℂ x)

    negativeBound : normℂ (-ℂ inverse) ≤ℝ rat (fst C)
    negativeBound = subst (_≤ℝ rat (fst C)) (sym (normℂ-neg inverse)) bounded

    scaledError : normℂ ((-ℂ inverse) ·ℂ ((y -ℂ x) -ℂ derivative ·ℂ (v -ℂ u))) ≤ℝ rat (fst (1₊ /2₊)) · h
    scaledError = boundedComplexErrorProduct (-ℂ inverse)
      ((y -ℂ x) -ℂ derivative ·ℂ (v -ℂ u)) h C (1₊ /2₊) negativeBound small

    inverseErrorBound : normℂ ((v -ℂ u) -ℂ inverse ·ℂ (y -ℂ x)) ≤ℝ rat (fst (1₊ /2₊)) · h
    inverseErrorBound = subst (λ e → normℂ e ≤ℝ rat (fst (1₊ /2₊)) · h)
      (sym (E.inverseError inverse derivative law x y u v)) scaledError

    linearBound : normℂ (inverse ·ℂ (y -ℂ x)) ≤ℝ a
    linearBound = normℂ-mulBound inverse (y -ℂ x) (rat (fst C))
      (normℂ (y -ℂ x)) bounded (≤ℝ-refl (normℂ (y -ℂ x)))

    sumBound : normℂ (((v -ℂ u) -ℂ inverse ·ℂ (y -ℂ x)) +ℂ inverse ·ℂ (y -ℂ x)) ≤ℝ rat (fst (1₊ /2₊)) · h + a
    sumBound = normℂ-addBound ((v -ℂ u) -ℂ inverse ·ℂ (y -ℂ x))
      (inverse ·ℂ (y -ℂ x)) (rat (fst (1₊ /2₊)) · h) a inverseErrorBound linearBound

    absorbed : h ≤ℝ a + rat (fst (1₊ /2₊)) · h
    absorbed = subst (h ≤ℝ_) (addComm (rat (fst (1₊ /2₊)) · h) a)
      (subst (_≤ℝ rat (fst (1₊ /2₊)) · h + a)
        (cong normℂ (ℂRing.minusPlus (v -ℂ u) (inverse ·ℂ (y -ℂ x)))) sumBound)

    doubled : a + a ≡ rat (fst (C +₊ C)) · normℂ (y -ℂ x)
    doubled = sym (mulDistL (rat (fst C)) (rat (fst C)) (normℂ (y -ℂ x)))
      ∙ cong (_· normℂ (y -ℂ x)) (rat+rat (fst C) (fst C))


