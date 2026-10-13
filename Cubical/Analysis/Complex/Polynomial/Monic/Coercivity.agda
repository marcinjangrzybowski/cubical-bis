module Cubical.Analysis.Complex.Polynomial.Monic.Coercivity where

-- A finite Horner bound suffices for coercivity. No powers, root selection,
-- or compactness principle are needed. The deliberately generous radius
-- makes the induction work also for the constant monic polynomial 1.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Vec using ([]; _∷_)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as ⊥ using ()
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
import Cubical.Data.Rationals.Order as ℚ
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Located using (dichotomyℝ)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm using (normℂ)
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds
open import Cubical.Analysis.Complex.Polynomial.Monic

monicCoerciveRadius : ∀ {n} → MonicPolynomial n → ℝ
monicCoerciveRadius [] = 1ℝ
monicCoerciveRadius (a ∷ p) = (modulusℂ a + 1ℝ) + monicCoerciveRadius p

private
  ≤sumL : ∀ x y → 0ℝ ≤ℝ y → x ≤ℝ x + y
  ≤sumL x y y≥0 = subst (_≤ℝ x + y) (addIdR x) (addPres≤L 0ℝ y x y≥0)

  ≤sumR : ∀ x y → 0ℝ ≤ℝ x → y ≤ℝ x + y
  ≤sumR x y x≥0 = subst (_≤ℝ x + y) (addIdL y) (addPres≤R 0ℝ x y x≥0)

  head-nonnegative : ∀ a → 0ℝ ≤ℝ modulusℂ a + 1ℝ
  head-nonnegative a = ≤ℝ-trans 0ℝ (modulusℂ a) (modulusℂ a + 1ℝ)
    (modulusℂ-nonnegative a) (≤sumL (modulusℂ a) 1ℝ
      (isNonnegative→0≤ 1ℝ oneIsNonnegative))

opaque
  monicCoerciveRadius-nonnegative : ∀ {n} (p : MonicPolynomial n) →
    0ℝ ≤ℝ monicCoerciveRadius p
  monicCoerciveRadius-nonnegative [] = isNonnegative→0≤ 1ℝ oneIsNonnegative
  monicCoerciveRadius-nonnegative (a ∷ p) =
    ≤ℝ-trans 0ℝ (modulusℂ a + 1ℝ) (monicCoerciveRadius (a ∷ p))
      (head-nonnegative a)
      (≤sumL (modulusℂ a + 1ℝ) (monicCoerciveRadius p)
        (monicCoerciveRadius-nonnegative p))

  evaluateMonic-coercive : ∀ {n} (p : MonicPolynomial n) z →
    monicCoerciveRadius p ≤ℝ modulusℂ z →
    1ℝ ≤ℝ modulusℂ (evaluateMonic p z)
  evaluateMonic-coercive [] z outside =
    subst (1ℝ ≤ℝ_) (sym modulusℂ-one) (≤ℝ-refl 1ℝ)
  evaluateMonic-coercive (a ∷ p) z outside =
    addReflects≤R 1ℝ (modulusℂ value) (modulusℂ a)
      (≤ℝ-trans (1ℝ + modulusℂ a) (modulusℂ z) (modulusℂ value + modulusℂ a)
        (subst (_≤ℝ modulusℂ z) (addComm (modulusℂ a) 1ℝ)
          (≤ℝ-trans (modulusℂ a + 1ℝ) (monicCoerciveRadius (a ∷ p))
            (modulusℂ z)
            (≤sumL (modulusℂ a + 1ℝ) (monicCoerciveRadius p)
              (monicCoerciveRadius-nonnegative p)) outside))
        (≤ℝ-trans (modulusℂ z) (modulusℂ (z ·ℂ tail))
          (modulusℂ value + modulusℂ a) product-lower product-upper))
    where
    tail : ℂ
    tail = evaluateMonic p z
    value : ℂ
    value = a +ℂ z ·ℂ tail

    tail-lower : 1ℝ ≤ℝ modulusℂ tail
    tail-lower = evaluateMonic-coercive p z
      (≤ℝ-trans (monicCoerciveRadius p) (monicCoerciveRadius (a ∷ p)) (modulusℂ z)
        (≤sumR (modulusℂ a + 1ℝ) (monicCoerciveRadius p) (head-nonnegative a)) outside)

    product-lower : modulusℂ z ≤ℝ modulusℂ (z ·ℂ tail)
    product-lower = subst2 _≤ℝ_ (mulIdR (modulusℂ z)) (sym (modulusℂ-mul z tail))
      (mulPres≤L 1ℝ (modulusℂ tail) (modulusℂ z)
        (0≤→isNonnegative (modulusℂ z) (modulusℂ-nonnegative z)) tail-lower)

    recover-product : value +ℂ (-ℂ a) ≡ z ·ℂ tail
    recover-product = cong (_+ℂ (-ℂ a)) (+ℂComm a (z ·ℂ tail))
      ∙ sym (+ℂAssoc (z ·ℂ tail) a (-ℂ a))
      ∙ cong (z ·ℂ tail +ℂ_) (+ℂInvR a) ∙ +ℂIdR (z ·ℂ tail)

    product-upper : modulusℂ (z ·ℂ tail) ≤ℝ modulusℂ value + modulusℂ a
    product-upper = subst2 _≤ℝ_ (cong modulusℂ recover-product)
      (cong (modulusℂ value +_) (modulusℂ-neg a)) (modulusℂ-triangle value (-ℂ a))

  -- Locatedness with a fixed margin avoids classical contraposition:
  -- a residual below 1 forces the point inside this slightly larger disk.
  smallResidual-modulusBound : ∀ {n} (p : MonicPolynomial n) z →
    modulusℂ (evaluateMonic p z) <ℝ 1ℝ →
    modulusℂ z <ℝ monicCoerciveRadius p + 1ℝ
  smallResidual-modulusBound p z small =
    PT.rec (isProp<ℝ (modulusℂ z) (monicCoerciveRadius p + 1ℝ)) cases
    (dichotomyℝ (monicCoerciveRadius p) (modulusℂ z) (monicCoerciveRadius p + 1ℝ)
      (subst (_<ℝ monicCoerciveRadius p + 1ℝ) (addIdR (monicCoerciveRadius p))
        (<ℝ-addL 0ℝ 1ℝ (monicCoerciveRadius p) (<ℚ→<ℝ 0 1 (ℚ.pos<pos tt)))))
    where
    cases : (modulusℂ z <ℝ monicCoerciveRadius p + 1ℝ) ⊎
      (monicCoerciveRadius p <ℝ modulusℂ z) →
      modulusℂ z <ℝ monicCoerciveRadius p + 1ℝ
    cases (inl inside) = inside
    cases (inr outside) = ⊥.rec (≤ℝ→≯ 1ℝ (modulusℂ (evaluateMonic p z))
      (evaluateMonic-coercive p z (<ℝ-weaken (monicCoerciveRadius p) (modulusℂ z) outside)) small)

  smallResidual-normBound : ∀ {n} (p : MonicPolynomial n) z →
    modulusℂ (evaluateMonic p z) <ℝ 1ℝ →
    normℂ z ≤ℝ (monicCoerciveRadius p + 1ℝ) + (monicCoerciveRadius p + 1ℝ)
  smallResidual-normBound p z small = ≤ℝ-trans (normℂ z)
    (modulusℂ z + modulusℂ z) ((monicCoerciveRadius p + 1ℝ) + (monicCoerciveRadius p + 1ℝ))
    (normℂ≤twiceModulusℂ z)
    (addPres≤ (modulusℂ z) (monicCoerciveRadius p + 1ℝ)
      (modulusℂ z) (monicCoerciveRadius p + 1ℝ) bounded bounded)
    where
    bounded : modulusℂ z ≤ℝ monicCoerciveRadius p + 1ℝ
    bounded = <ℝ-weaken (modulusℂ z) (monicCoerciveRadius p + 1ℝ)
      (smallResidual-modulusBound p z small)
