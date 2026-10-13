module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Absorption where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Shrink
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Constants

opaque
  halfBoundFromSlack : ∀ B s ε → ε ≤ℝ descentHalf · B → B <ℝ s + ε → descentHalf · B <ℝ s
  halfBoundFromSlack B s ε small below = <ℝ-addR-cancel (descentHalf · B) s (descentHalf · B)
    (subst (_<ℝ s + descentHalf · B) (sym (halfScaleDouble B))
      (<≤ℝ-trans B (s + ε) (s + descentHalf · B) below (addPres≤L ε (descentHalf · B) s small)))

  selectedBelowConstant : ∀ A s ε → ε ≤ℝ descentHalf · A → s <ℝ descentHalf · A + ε → s <ℝ A
  selectedBelowConstant A s ε small below =
    subst (s <ℝ_) (halfScaleDouble A)
      (<≤ℝ-trans s (descentHalf · A + ε) (descentHalf · A + descentHalf · A) below
        (addPres≤L ε (descentHalf · A) (descentHalf · A) small))

  remainderBelowHalf : ∀ B s remainder error → descentHalf · B <ℝ s →
    error ≤ℝ descentEighth · B → remainder ≤ℝ descentShrink · s + error → remainder <ℝ descentHalf · s
  remainderBelowHalf B s remainder error selected error-small remainder-bound =
    ≤<ℝ-trans remainder (descentShrink · s + descentEighth · B) (descentHalf · s)
      (≤ℝ-trans remainder (descentShrink · s + error) (descentShrink · s + descentEighth · B) remainder-bound
        (addPres≤L error (descentEighth · B) (descentShrink · s) error-small))
      (subst (descentShrink · s + descentEighth · B <ℝ_) (quarterScaleDouble s)
        (<ℝ-addL (descentEighth · B) (descentShrink · s) (descentShrink · s)
          (subst (_<ℝ descentShrink · s) (quarterScaleHalf B)
            (mulPres<PosL (descentHalf · B) s descentShrink descentShrink-positive selected))))

  -- The constant and selected term cancel exactly; the residual sum is
  -- small enough to leave a degree-controlled improvement.
  absorbedCancellationBound : ∀ A B s remainder value → s <ℝ A → descentHalf · B <ℝ s →
    remainder <ℝ descentHalf · s → value ≤ℝ absℝ (A - s) + remainder →
    value <ℝ A - descentShrink · B
  absorbedCancellationBound A B s remainder value selected-upper selected-lower remainder-small value-bound =
    ≤<ℝ-trans value (absℝ (A - s) + remainder) (A - descentShrink · B) value-bound
      (subst (_<ℝ A - descentShrink · B)
        (sym (cong (_+ remainder) (absOfNonnegative (A - s) (nonnegativeSub s A (<ℝ-weaken s A selected-upper)))))
        (<ℝ-trans ((A - s) + remainder) (A - descentHalf · s) (A - descentShrink · B)
          (subst ((A - s) + remainder <ℝ_) (subtractHalfCancel A s)
            (<ℝ-addL remainder (descentHalf · s) (A - s) remainder-small))
          (subst (A - descentHalf · s <ℝ_) (cong (λ value → A - value) (halfScaleHalf B))
            (<ℝ-addL (- (descentHalf · s)) (- (descentHalf · (descentHalf · B))) A
              (<ℝ-neg (descentHalf · (descentHalf · B)) (descentHalf · s)
                (mulPres<PosL (descentHalf · B) s descentHalf descentHalf-positive selected-lower))))))
