module Cubical.HITs.CauchyReals.Circle.Homotopy.IntervalLift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.UniformGroup
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Winding.Continuity
open import Cubical.HITs.CauchyReals.Circle.Winding.Lift using (shortAngle-identify)
open import Cubical.HITs.CauchyReals.Circle.Homotopy.RealPaths
open import Cubical.HITs.CauchyReals.Circle.Homotopy.LocalLift
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures using (_∘UC_)

-- A lift of a clamped interval path, normalized at its left endpoint.
-- The bounded extension is constant outside the interval.
record IntervalLift (f : CirclePath) (a b : ℚ) : Type where
  field
    path : RealPath
    covers : ∀ t → fst f (rat a) ℝS¹.+ cover (fst path t) ≡
      fst f (clampᵣ (rat a) (rat b) t)
    lower : ∀ t → t ≤ᵣ rat a → fst path t ≡ 0
    upper : ∀ t → rat b ≤ᵣ t → fst path t ≡ fst path (rat b)
    bound : ℝ₊
    bounded : ∀ t → absᵣ (fst path t) ≤ᵣ fst bound

open IntervalLift

joinIntervalLift : (f : CirclePath) (a m b : ℚ) → a ℚ.≤ m → m ℚ.≤ b →
  IntervalLift f a m → IntervalLift f m b → IntervalLift f a b
joinIntervalLift f a m b am mb left right = result
  where
  amᵣ : rat a ≤ᵣ rat m
  amᵣ = ≤ℚ→≤ᵣ a m am
  mbᵣ : rat m ≤ᵣ rat b
  mbᵣ = ≤ℚ→≤ᵣ m b mb
  joined : RealPath
  joined = addRealUC (path left) (path right)
  projected : CirclePath
  projected = addDistCircleUC (constantUC (fst f (rat a))) (coverUC ∘UC joined)
  target : CirclePath
  target = f ∘UC clampUC (rat a) (rat b)

  on-left : ∀ t → t ≤ᵣ rat m → fst projected t ≡ fst target t
  on-left t tm = cong (λ z → fst f (rat a) ℝS¹.+ cover z)
    (cong (fst (path left) t +ᵣ_) (lower right t tm) ∙ +IdR (fst (path left) t))
    ∙ covers left t
    ∙ cong (fst f) (clamp-left (rat a) (rat m) (rat b) t amᵣ mbᵣ tm)

  at-middle : fst f (rat a) ℝS¹.+ cover (fst (path left) (rat m)) ≡ fst f (rat m)
  at-middle = covers left (rat m) ∙ cong (fst f)
    (≤x→clampᵣ≡ (rat a) (rat m) (rat m) amᵣ (≤ᵣ-refl (rat m)))

  on-right : ∀ t → rat m ≤ᵣ t → fst projected t ≡ fst target t
  on-right t mt = cong (λ z → fst f (rat a) ℝS¹.+ cover (z +ᵣ fst (path right) t))
    (upper left t mt)
    ∙ cong (fst f (rat a) ℝS¹.+_)
      (cover-add (fst (path left) (rat m)) (fst (path right) t))
    ∙ ℝS¹.+Assoc (fst f (rat a)) (cover (fst (path left) (rat m))) (cover (fst (path right) t))
    ∙ cong (ℝS¹._+ cover (fst (path right) t)) at-middle
    ∙ covers right t
    ∙ cong (fst f) (clamp-right (rat a) (rat m) (rat b) t amᵣ mbᵣ mt)

  result : IntervalLift f a b
  path result = joined
  covers result = circlePath-split m projected target on-left on-right
  lower result t ta = cong₂ _+ᵣ_ (lower left t ta)
    (lower right t (isTrans≤ᵣ t (rat a) (rat m) ta amᵣ)) ∙ +ᵣ-rat 0 0
  upper result t bt = cong₂ _+ᵣ_
    (upper left t (isTrans≤ᵣ (rat m) (rat b) t mbᵣ bt) ∙ sym (upper left (rat b) mbᵣ))
    (upper right t bt)
  bound result = bound left ₊+ᵣ bound right
  bounded result t = isTrans≤ᵣ _ _ _ (absᵣ-triangle (fst (path left) t) (fst (path right) t))
    (≤ᵣMonotone+ᵣ _ _ _ _ (bounded left t) (bounded right t))

-- Each leaf comes with a uniform small-image condition. Its angle is
-- taken in one chart, so the bound is independent of the chosen leaf.
smallIntervalLift : (f : CirclePath) (a b : ℚ) → a ℚ.≤ b →
  (∀ t → PremetricStr._≈[_]_ (snd distCirclePremetricSpace)
    (fst f (clampᵣ (rat a) (rat b) t)) localLiftRadius (fst f (rat a))) →
  IntervalLift f a b
smallIntervalLift f a b ab close = result
  where
  clamped : CirclePath
  clamped = f ∘UC clampUC (rat a) (rat b)
  clamped-β : ∀ t → fst clamped t ≡ fst f (clampᵣ (rat a) (rat b) t)
  clamped-β t = refl
  clamped-close : ∀ t → PremetricStr._≈[_]_ (snd distCirclePremetricSpace)
    (fst clamped t) localLiftRadius (fst f (rat a))
  clamped-close t = subst (λ z → PremetricStr._≈[_]_ (snd distCirclePremetricSpace)
    z localLiftRadius (fst f (rat a))) (sym (clamped-β t)) (close t)
  lifted : RealPath
  lifted = localLiftUC {M = ℝPremetricSpace} (fst f (rat a)) clamped
  abᵣ : rat a ≤ᵣ rat b
  abᵣ = ≤ℚ→≤ᵣ a b ab
  lifted-covers : ∀ t → fst f (rat a) ℝS¹.+ cover (fst lifted t) ≡ fst clamped t
  lifted-covers t = localLift-near {M = ℝPremetricSpace} (fst f (rat a)) clamped t (clamped-close t)
  lifted-lower : ∀ t → t ≤ᵣ rat a → fst lifted t ≡ 0
  lifted-lower t ta = localLift-centre {M = ℝPremetricSpace} (fst f (rat a)) clamped t
    (clamped-β t ∙ cong (fst f) (x≤→clampᵣ≡ (rat a) (rat b) t abᵣ ta))
  lifted-upper : ∀ t → rat b ≤ᵣ t → fst lifted t ≡ fst lifted (rat b)
  lifted-upper t bt = localLift-cong {M = ℝPremetricSpace} (fst f (rat a)) clamped t (rat b)
    (clamped-β t ∙ cong (fst f) (≤x→clampᵣ≡ (rat a) (rat b) t abᵣ bt
      ∙ sym (≤x→clampᵣ≡ (rat a) (rat b) (rat b) abᵣ (≤ᵣ-refl (rat b)))) ∙ sym (clamped-β (rat b)))
  lifted-bounded : ∀ t → absᵣ (fst lifted t) ≤ᵣ 1
  lifted-bounded t = <ᵣWeaken≤ᵣ _ _ (isTrans<ᵣ _ (rat [ 1 / 4 ]) 1
    (localLift-near-bound {M = ℝPremetricSpace} (fst f (rat a)) clamped t (clamped-close t)) decℚ<ᵣ?)
  result : IntervalLift f a b
  path result = lifted
  covers result t = lifted-covers t ∙ clamped-β t
  lower result = lifted-lower
  upper result = lifted-upper
  bound result = 1
  bounded result = lifted-bounded

joinIntervalLift-endpoint : (f : CirclePath) (a m b : ℚ) (am : a ℚ.≤ m) (mb : m ℚ.≤ b)
  (left : IntervalLift f a m) (right : IntervalLift f m b) →
  fst (path (joinIntervalLift f a m b am mb left right)) (rat b) ≡
    fst (path left) (rat m) +ᵣ fst (path right) (rat b)
joinIntervalLift-endpoint f a m b am mb left right =
  cong (_+ᵣ fst (path right) (rat b)) (upper left (rat b) (≤ℚ→≤ᵣ m b mb))

smallIntervalLift-endpoint : (f : CirclePath) (a b : ℚ) (ab : a ℚ.≤ b)
  (close : ∀ t → PremetricStr._≈[_]_ (snd distCirclePremetricSpace)
    (fst f (clampᵣ (rat a) (rat b) t)) localLiftRadius (fst f (rat a))) →
  (near : Near (fst f (rat a)) (fst f (rat b))) →
  fst (path (smallIntervalLift f a b ab close)) (rat b) ≡ shortAngle (fst f (rat a)) (fst f (rat b)) near
smallIntervalLift-endpoint f a b ab close near = sym
  (shortAngle-identify (fst f (rat a)) (fst f (rat b)) near _ endpoint-bound step)
  where
  clamped : CirclePath
  clamped = f ∘UC clampUC (rat a) (rat b)
  clamped-β : ∀ t → fst clamped t ≡ fst f (clampᵣ (rat a) (rat b) t)
  clamped-β t = refl
  endpoint-bound : absᵣ (fst (path (smallIntervalLift f a b ab close)) (rat b)) <ᵣ rat [ 1 / 4 ]
  endpoint-bound = localLift-near-bound {M = ℝPremetricSpace} (fst f (rat a)) clamped (rat b)
    (subst (λ z → PremetricStr._≈[_]_ (snd distCirclePremetricSpace)
      z localLiftRadius (fst f (rat a))) (sym (clamped-β (rat b))) (close (rat b)))
  step : fst f (rat a) ℝS¹.+ cover (fst (path (smallIntervalLift f a b ab close)) (rat b)) ≡ fst f (rat b)
  step = covers (smallIntervalLift f a b ab close) (rat b) ∙ cong (fst f)
    (≤x→clampᵣ≡ (rat a) (rat b) (rat b) (≤ℚ→≤ᵣ a b ab) (≤ᵣ-refl (rat b)))
