module Cubical.Analysis.Complex.Modulus.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Functions.SquareRoot.Order
open import Cubical.Analysis.Real.Functions.SquareRoot.Estimates
open import Cubical.Analysis.Real.Functions.SquareRoot.Nonnegative
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Conjugation
open import Cubical.Analysis.Complex.NormSquared
open import Cubical.Analysis.Complex.Norm
import Cubical.Analysis.Complex.Modulus.Algebra as AlgebraDefinition
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

private
  module A = AlgebraDefinition.ModulusAlgebra ℝCommRing
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

open import Cubical.Analysis.Complex.Modulus.Base

reAbs≤modulusℂ : ∀ z → absℝ (re z) ≤ℝ modulusℂ z
reAbs≤modulusℂ z = squareReflects≤Nonnegative (absℝ (re z)) (modulusℂ z)
  (modulusℂ-nonnegative z)
  (subst2 _≤ℝ_ (sym (absSquared (re z))) (sym (modulusℂ-square z))
    (subst (_≤ℝ normSq z) (addIdR (re z · re z))
      (addPres≤L 0ℝ (im z · im z) (re z · re z)
        (isNonnegative→0≤ _ (squareIsNonnegative (im z))))))

imAbs≤modulusℂ : ∀ z → absℝ (im z) ≤ℝ modulusℂ z
imAbs≤modulusℂ z = squareReflects≤Nonnegative (absℝ (im z)) (modulusℂ z)
  (modulusℂ-nonnegative z)
  (subst2 _≤ℝ_ (sym (absSquared (im z))) (sym (modulusℂ-square z))
    (subst (_≤ℝ normSq z) (addIdL (im z · im z))
      (addPres≤R 0ℝ (re z · re z) (im z · im z)
        (isNonnegative→0≤ _ (squareIsNonnegative (re z))))))

modulusℂ≤normℂ : ∀ z → modulusℂ z ≤ℝ normℂ z
modulusℂ≤normℂ z = squareReflects≤Nonnegative (modulusℂ z) (normℂ z)
  (normℂ-nonnegative z)
  (subst (_≤ℝ normℂ z · normℂ z)
    (cong₂ _+_ (absSquared (re z)) (absSquared (im z)) ∙ sym (modulusℂ-square z))
    (squareSumBound (absℝ (re z)) (absℝ (im z)) (absNonnegative (re z)) (absNonnegative (im z))))

normℂ≤twiceModulusℂ : ∀ z → normℂ z ≤ℝ modulusℂ z + modulusℂ z
normℂ≤twiceModulusℂ z = addPres≤ (absℝ (re z)) (modulusℂ z)
  (absℝ (im z)) (modulusℂ z) (reAbs≤modulusℂ z) (imAbs≤modulusℂ z)

modulusℂ-zeroReflects : ∀ z → modulusℂ z ≤ℝ 0ℝ → z ≡ 0ℂ
modulusℂ-zeroReflects z bounded = normℂ-zeroReflects z
  (≤ℝ-trans (normℂ z) (modulusℂ z + modulusℂ z) 0ℝ (normℂ≤twiceModulusℂ z)
    (subst (modulusℂ z + modulusℂ z ≤ℝ_) (addIdR 0ℝ)
      (addPres≤ (modulusℂ z) 0ℝ (modulusℂ z) 0ℝ bounded bounded)))

opaque
  modulusℂ-triangle : ∀ z w → modulusℂ (z +ℂ w) ≤ℝ modulusℂ z + modulusℂ w
  modulusℂ-triangle z w = squareReflects≤Nonnegative (modulusℂ (z +ℂ w))
    (modulusℂ z + modulusℂ w)
    (isNonnegative→0≤ _ (addPresIsNonnegative _ _
      (0≤→isNonnegative _ (modulusℂ-nonnegative z))
      (0≤→isNonnegative _ (modulusℂ-nonnegative w))))
    (subst2 _≤ℝ_ (sym (modulusℂ-square (z +ℂ w) ∙ A.normSq-add z w))
      (sym (A.squareSumExpansion (modulusℂ z) (modulusℂ w)
        ∙ cong (_+ (modulusℂ z · modulusℂ w + modulusℂ z · modulusℂ w))
          (cong₂ _+_ (modulusℂ-square z) (modulusℂ-square w))))
      (addPres≤L (dot + dot) (product + product) (normSq z + normSq w)
        (addPres≤ dot product dot product dot-bound dot-bound)))
    where
    dot : ℝ
    dot = re (z ·ℂ conjugate w)
    product : ℝ
    product = modulusℂ z · modulusℂ w

    dot-bound : dot ≤ℝ product
    dot-bound = ≤ℝ-trans dot (absℝ dot) product (leAbs dot)
      (subst (absℝ dot ≤ℝ_)
        (modulusℂ-mul z (conjugate w) ∙ cong (modulusℂ z ·_) (modulusℂ-conjugate w))
        (reAbs≤modulusℂ (z ·ℂ conjugate w)))
