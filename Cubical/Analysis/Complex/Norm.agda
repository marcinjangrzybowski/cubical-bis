module Cubical.Analysis.Complex.Norm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Conjugation
open import Cubical.Analysis.Complex.Sequence
import Cubical.Analysis.Complex.Algebra.Identities as IdentitiesDefinition

private
  module R = IdentitiesDefinition.Identities ℝCommRing

-- The l1 norm supplies submultiplicative estimates without a square root.
-- It is not asserted to be multiplicative like the Euclidean modulus.
normℂ : ℂ → ℝ
normℂ z = absℝ (re z) + absℝ (im z)

normℂ-nonnegative : ∀ z → 0ℝ ≤ℝ normℂ z
normℂ-nonnegative z = isNonnegative→0≤ (normℂ z)
  (addPresIsNonnegative (absℝ (re z)) (absℝ (im z))
    (absIsNonnegative (re z)) (absIsNonnegative (im z)))

normℂ-zero : normℂ 0ℂ ≡ 0ℝ
normℂ-zero = cong₂ _+_ absZero absZero ∙ addIdR 0ℝ

normℂ-one : normℂ 1ℂ ≡ 1ℝ
normℂ-one = cong₂ _+_ absOne absZero ∙ addIdR 1ℝ

normℂ-neg : ∀ z → normℂ (-ℂ z) ≡ normℂ z
normℂ-neg z = cong₂ _+_ (absNeg (re z)) (absNeg (im z))

normℂ-conjugate : ∀ z → normℂ (conjugate z) ≡ normℂ z
normℂ-conjugate z = cong (absℝ (re z) +_) (absNeg (im z))

normℂ-fromℝ : ∀ x → normℂ (fromℝ x) ≡ absℝ x
normℂ-fromℝ x = cong (absℝ x +_) absZero ∙ addIdR (absℝ x)

reAbs≤normℂ : ∀ z → absℝ (re z) ≤ℝ normℂ z
reAbs≤normℂ z = subst (_≤ℝ normℂ z) (addIdR (absℝ (re z)))
  (addPres≤L 0ℝ (absℝ (im z)) (absℝ (re z)) (absNonnegative (im z)))

imAbs≤normℂ : ∀ z → absℝ (im z) ≤ℝ normℂ z
imAbs≤normℂ z = subst (_≤ℝ normℂ z) (addIdL (absℝ (im z)))
  (addPres≤R 0ℝ (absℝ (re z)) (absℝ (im z)) (absNonnegative (re z)))

opaque
  normℂ-triangle : ∀ z w → normℂ (z +ℂ w) ≤ℝ normℂ z + normℂ w
  normℂ-triangle (a , b) (c , d) =
    subst (normℂ ((a , b) +ℂ (c , d)) ≤ℝ_)
      (R.shuffle (absℝ a) (absℝ c) (absℝ b) (absℝ d))
      (addPres≤ (absℝ (a + c)) (absℝ a + absℝ c)
        (absℝ (b + d)) (absℝ b + absℝ d)
        (absTriangle a c) (absTriangle b d))

  normℂ-submultiplicative : ∀ z w → normℂ (z ·ℂ w) ≤ℝ normℂ z · normℂ w
  normℂ-submultiplicative (a , b) (c , d) =
    subst (normℂ ((a , b) ·ℂ (c , d)) ≤ℝ_)
      (cong₂ _+_
        (cong₂ _+_ (absMul a c) (absMul b d))
        (cong₂ _+_ (absMul a d) (absMul b c))
      ∙ R.productBoundExpansion (absℝ a) (absℝ b) (absℝ c) (absℝ d))
      (addPres≤ (absℝ (a · c - b · d)) (absℝ (a · c) + absℝ (b · d))
        (absℝ (a · d + b · c)) (absℝ (a · d) + absℝ (b · c))
        (absSubTriangle (a · c) (b · d)) (absTriangle (a · d) (b · c)))

  normℂ-subtriangle : ∀ z w → normℂ (z -ℂ w) ≤ℝ normℂ z + normℂ w
  normℂ-subtriangle z w = subst (normℂ (z -ℂ w) ≤ℝ_)
    (cong (normℂ z +_) (normℂ-neg w)) (normℂ-triangle z (-ℂ w))

normℂ-preservesLimit : ∀ {z l} → IsComplexLimit z l →
  isLimitSequence (normℂ ∘ z) (normℂ l)
normℂ-preservesLimit (r , i) = addPresIsLimitSequence
  (continuousPreservesIsLimitSequence absℝ abs-isContinuous r)
  (continuousPreservesIsLimitSequence absℝ abs-isContinuous i)

private
  absBoundZero : ∀ x → absℝ x ≤ℝ 0ℝ → x ≡ 0ℝ
  absBoundZero x bounded = ≤ℝ-antisym x 0ℝ
    (≤ℝ-trans x (absℝ x) 0ℝ (leAbs x) bounded)
    (subst2 _≤ℝ_ negZero (negInvol x)
      (negPres≤ (- x) 0ℝ
        (≤ℝ-trans (- x) (absℝ x) 0ℝ (negLeAbs x) bounded)))

normℂ-zeroReflects : ∀ z → normℂ z ≤ℝ 0ℝ → z ≡ 0ℂ
normℂ-zeroReflects z bounded = ℂ≡
  (absBoundZero (re z) (≤ℝ-trans (absℝ (re z)) (normℂ z) 0ℝ (reAbs≤normℂ z) bounded))
  (absBoundZero (im z) (≤ℝ-trans (absℝ (im z)) (normℂ z) 0ℝ (imAbs≤normℂ z) bounded))

normℂ-difference-zero : ∀ z w → normℂ (z -ℂ w) ≤ℝ 0ℝ → z ≡ w
normℂ-difference-zero z w bounded = ℂRing.equalByDifference z w
  (normℂ-zeroReflects (z -ℂ w) bounded)
