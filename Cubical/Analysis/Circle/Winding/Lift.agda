module Cubical.Analysis.Circle.Winding.Lift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Base as ℚ using (ℚ; [_/_])
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Order.Algebra as ℚ
import Cubical.Data.Rationals.Inverse as ℚ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Integer
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Circle.Base
open import Cubical.Analysis.Circle.Metric
open import Cubical.Analysis.Circle.Winding.Angle
open import Cubical.Analysis.Circle.Winding.Subdivision
open import Cubical.Analysis.Circle.Winding.Loop

lift-step : ∀ (f : ℝ → Circle) base (g : ℝ → ℝ) →
  (∀ t → f t ≡ base +ᶜ cover (g t)) → ∀ x y →
  f x +ᶜ cover (g y - g x) ≡ f y
lift-step f base g lifts x y =
  cong (_+ᶜ cover (g y - g x)) (lifts x)
  ∙ sym (circle-add-assoc base (cover (g x)) (cover (g y - g x)))
  ∙ cong (base +ᶜ_)
    (sym (cover-add (g x) (g y - g x))
    ∙ cong cover (addComm (g x) (g y - g x) ∙ subAddCancel (g y) (g x)))
  ∙ sym (lifts y)

private
  telescope : ∀ x y z → (y - x) + (z - y) ≡ z - x
  telescope x y z = addComm (y - x) (z - y)
    ∙ addAssoc (z - y) y (- x) ∙ cong (_+ (- x)) (subAddCancel z y)

  module LiftSum (f : ℝ → Circle) (g : ℝ → ℝ)
    (step : ∀ x y → f x +ᶜ cover (g y - g x) ≡ f y)
    (δ : ℚ₊)
    (close : ∀ x y → x ∼[ δ ] y → g x ∼[ quarter ] g y)
    where

    module SD = Subdivision (f ∘ rat)

    turns-lift : ∀ n a b a≤b fine → mesh n a b ℚ.< fst δ →
      SD.turns n a b a≤b fine ≡ g (rat b) - g (rat a)
    turns-lift zero a b a≤b fine bound = shortAngle-unique
      (f (rat a)) (f (rat b)) (SD.endpoints a b a≤b fine) (g (rat b) - g (rat a))
      (sub-close-zero (g (rat b)) (g (rat a)) quarter
        (sym∼ (g (rat a)) (g (rat b)) quarter
          (close (rat a) (rat b) (rat-rat a b δ
            (ℚ.isTrans≤< _ (b ℚ.- a) _
              (interval-distance a b a b (ℚ.isRefl≤ a) a≤b a≤b (ℚ.isRefl≤ b))
              (subst (ℚ._< fst δ) (ℚ.·IdR (b ℚ.- a)) bound))))))
      (step (rat a) (rat b))
    turns-lift (suc n) a b a≤b fine bound =
      cong₂ _+_
        (turns-lift n a (mid a b) (mid-left a b a≤b) (fst fine)
          (subst (ℚ._< fst δ) (sym (mesh-left n a b)) bound))
        (turns-lift n (mid a b) b (mid-right a b a≤b) (snd fine)
          (subst (ℚ._< fst δ) (sym (mesh-right n a b)) bound))
      ∙ telescope (g (rat a)) (g (rat (mid a b))) (g (rat b))

-- The lift's modulus alone supplies both the small real increments and the
-- fine circle subdivision.  The circle modulus need not be selected again.
windingLoop-lift : (f : UC[ ℝPremetricSpace , CirclePremetricSpace ]) →
  (loop : fst f (rat 0) ≡ fst f (rat 1)) →
  (g : UC[ ℝPremetricSpace , ℝPremetricSpace ]) →
  (∀ x y → fst f x +ᶜ cover (fst g y - fst g x) ≡ fst f y) →
  integer (windingLoop f loop) ≡ fst g (rat 1) - fst g (rat 0)
windingLoop-lift f loop g step = PT.rec (isSetℝ _ _) calculate (snd g)
  where
  module SD = Subdivision (fst f ∘ rat)

  calculate : (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith
    (snd ℝPremetricSpace) (fst g) (snd ℝPremetricSpace) μ) →
    integer (windingLoop f loop) ≡ fst g (rat 1) - fst g (rat 0)
  calculate (μ , uc) = sym (windingLoop-subdivision f loop n fine)
    ∙ LiftSum.turns-lift (fst f) (fst g) step δ close n 0 1 unit-order fine bound
    where
    δ = μ quarter
    n = fst (ℚ.1/2ⁿ<ε δ)
    bound : mesh n 0 1 ℚ.< fst δ
    bound = subst (ℚ._< fst δ) (sym (ℚ.·IdL ([ 1 / 2 ] ℚ.^ⁿ n)))
      (snd (ℚ.1/2ⁿ<ε δ))
    close : ∀ x y → x ∼[ δ ] y → fst g x ∼[ quarter ] fst g y
    close x y = IsUniformlyContinuousWith.pres≈ uc x y quarter
    fine : SD.Fine n 0 1
    fine = SD.fine-from-mesh n 0 1 unit-order δ
      (λ x y near → ∣ fst g (rat y) - fst g (rat x) ,
        sub-close-zero (fst g (rat y)) (fst g (rat x)) quarter
          (sym∼ (fst g (rat x)) (fst g (rat y)) quarter
            (close (rat x) (rat y) (rat-rat x y δ near))) ,
        step (rat x) (rat y) ∣₁) bound
