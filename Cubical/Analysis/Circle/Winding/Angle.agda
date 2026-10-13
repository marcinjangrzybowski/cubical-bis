module Cubical.Analysis.Circle.Winding.Angle where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Circle.Base
open import Cubical.Analysis.Circle.Metric

Near : Circle → Circle → Type
Near p q = p ≈ᶜ[ quarter ] q

shortAngle : ∀ p q → Near p q → ℝ
shortAngle p q near = fst (shortDisplacement p q near)

shortAngle-bound : ∀ p q near → shortAngle p q near ∼[ quarter ] 0ℝ
shortAngle-bound p q near = fst (snd (shortDisplacement p q near))

shortAngle-step : ∀ p q near → p +ᶜ cover (shortAngle p q near) ≡ q
shortAngle-step p q near = snd (snd (shortDisplacement p q near))

-- Three short increments fit strictly inside one turn.  Integer separation
-- therefore makes local addition exact, which is the refinement invariant.
shortAngle-add : ∀ p q r pq qr pr →
  shortAngle p q pq + shortAngle q r qr ≡ shortAngle p r pr
shortAngle-add p q r pq qr pr =
  displacement-unique p r (quarter +₊ quarter) quarter (ℚ.pos≤pos tt)
    (a + b , small , step) (shortDisplacement p r pr)
  where
  a = shortAngle p q pq
  b = shortAngle q r qr
  small : (a + b) ∼[ quarter +₊ quarter ] 0ℝ
  small = subst (λ z → (a + b) ∼[ quarter +₊ quarter ] z) (addIdL 0ℝ)
    (add-pres∼ a 0ℝ b 0ℝ quarter quarter
      (shortAngle-bound p q pq) (shortAngle-bound q r qr))
  step : p +ᶜ cover (a + b) ≡ r
  step = cong (p +ᶜ_) (cover-add a b)
    ∙ circle-add-assoc p (cover a) (cover b)
    ∙ cong (_+ᶜ cover b) (shortAngle-step p q pq)
    ∙ shortAngle-step q r qr

shortAngle-unique : ∀ p q near t → t ∼[ quarter ] 0ℝ →
  p +ᶜ cover t ≡ q → shortAngle p q near ≡ t
shortAngle-unique p q near t bound step =
  displacement-unique p q quarter quarter (ℚ.pos≤pos tt)
    (shortDisplacement p q near) (t , bound , step)
