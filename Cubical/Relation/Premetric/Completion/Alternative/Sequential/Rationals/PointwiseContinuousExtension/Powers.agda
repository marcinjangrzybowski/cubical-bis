module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.PointwiseContinuousExtension.Powers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ hiding (isProp∼)
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.LocallyUniformlyContinuous
  as Local
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.PointwiseContinuousExtension
  as Exact

module S = Local.S
module E = Exact.E

open PositiveRationals
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing

private
  module Pℚ = PremetricStr (ℚPremetricSpace .snd)
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


-- No operation on completed rationals is used in the construction of this
-- function or in its estimate.

powℚ : ℕ → ℚ → ℚ
powℚ n q = q ℚ.^ⁿ n


private
  powAbs : ∀ q n → abs (powℚ n q) ≡ (abs q) ℚ.^ⁿ n
  powAbs q zero = 0<→abs≡id 1 0<1
  powAbs q (suc n) =
    sym (abs·abs q (powℚ n q))
    ∙ cong (abs q ·_) (powAbs q n)

  powBounded : ∀ B q n →
    abs q ≤ℚ fst B →
    abs (powℚ n q) ≤ℚ fst (B ℚ₊^ⁿ n)
  powBounded B q n absq≤B =
    subst (_≤ℚ fst (B ℚ₊^ⁿ n))
      (sym (powAbs q n))
      (powMono n (0≤abs q) absq≤B)

  telescopingDifference : ∀ x y z →
    (x - y) + (y - z) ≡ x - z
  telescopingDifference x y z =
    (x + (- y)) + (y + (- z))
      ≡⟨ ℚ.+Assoc (x + (- y)) y (- z) ⟩
    ((x + (- y)) + y) + (- z)
      ≡⟨ cong (_+ (- z)) (sym (ℚ.+Assoc x (- y) y)) ⟩
    (x + ((- y) + y)) + (- z)
      ≡⟨ cong (λ w → (x + w) + (- z)) (ℚ.+InvL y) ⟩
    (x + 0) + (- z)
      ≡⟨ cong (_+ (- z)) (ℚ.+IdR x) ⟩
    x - z ∎

  multiplyDifference : ∀ a b c d →
    a · b - c · d ≡
      (a - c) · b + c · (b - d)
  multiplyDifference a b c d =
    sym (telescopingDifference (a · b) (c · b) (c · d))
    ∙ cong₂ _+_
        (sym (ℚRing.·DistL- a c b))
        (sym (ℚRing.·DistR- c b d))


-- A deliberately loose positive constant is used at exponent zero.  For a
-- successor, the two summands correspond to the two terms in the ordinary
-- telescoping product estimate.

powerLipschitzConstant : ℚ₊ → ℕ → ℚ₊
powerLipschitzConstant B zero = 1
powerLipschitzConstant B (suc n) =
  (B ℚ₊^ⁿ n) +₊ (B ·₊ powerLipschitzConstant B n)


powerℚ-lipschitzOnBall : ∀ n B →
  Local.LL.IsLipschitzOnBallWith
    (powℚ n) B (powerLipschitzConstant B n)
powerℚ-lipschitzOnBall zero B
  .Local.LL.IsLipschitzOnBallWith.pres≈
    x y ε absx≤B absy≤B x≈y =
    Pℚ.isRefl≈ 1 ((powerLipschitzConstant B zero) ·₊ ε)
powerℚ-lipschitzOnBall (suc n) B
  .Local.LL.IsLipschitzOnBallWith.pres≈
    x y ε absx≤B absy≤B x≈y =
    subst (abs (powℚ (suc n) x - powℚ (suc n) y) <ℚ_)
      factor (isTrans≤< _ _ _ estimate strict)
  where
    L = powerLipschitzConstant B n
    Bⁿ = B ℚ₊^ⁿ n

    previous≈ : powℚ n x Pℚ.≈[ L ·₊ ε ] powℚ n y
    previous≈ = powerℚ-lipschitzOnBall n B
      .Local.LL.IsLipschitzOnBallWith.pres≈
        x y ε absx≤B absy≤B x≈y

    sumOfProducts =
      abs (x - y) · fst Bⁿ +
      fst B · abs (powℚ n x - powℚ n y)

    triangleStep :
      abs (powℚ (suc n) x - powℚ (suc n) y) ≤ℚ
        abs ((x - y) · powℚ n x) +
        abs (y · (powℚ n x - powℚ n y))
    triangleStep =
      subst
        (λ z → abs z ≤ℚ
          abs ((x - y) · powℚ n x) +
          abs (y · (powℚ n x - powℚ n y)))
        (sym (multiplyDifference x (powℚ n x) y (powℚ n y)))
        (triangularInequality
          ((x - y) · powℚ n x)
          (y · (powℚ n x - powℚ n y)))

    absoluteProducts :
      abs ((x - y) · powℚ n x) +
        abs (y · (powℚ n x - powℚ n y)) ≡
      abs (x - y) · abs (powℚ n x) +
        abs y · abs (powℚ n x - powℚ n y)
    absoluteProducts = cong₂ _+_
      (sym (abs·abs (x - y) (powℚ n x)))
      (sym (abs·abs y (powℚ n x - powℚ n y)))

    boundedStep :
      abs (x - y) · abs (powℚ n x) +
        abs y · abs (powℚ n x - powℚ n y) ≤ℚ
      sumOfProducts
    boundedStep = +Mono≤ _ _ _ _
      (·MonoL≤ (abs (powℚ n x)) (fst Bⁿ) (abs (x - y))
        (0≤abs (x - y)) (powBounded B x n absx≤B))
      (·MonoR≤ (abs y) (fst B) (abs (powℚ n x - powℚ n y))
        (0≤abs (powℚ n x - powℚ n y)) absy≤B)

    estimate :
      abs (powℚ (suc n) x - powℚ (suc n) y) ≤ℚ
        sumOfProducts
    estimate = isTrans≤ _ _ _ triangleStep
      (subst (_≤ℚ sumOfProducts) (sym absoluteProducts) boundedStep)

    strict : sumOfProducts <ℚ
      fst ε · fst Bⁿ + fst B · (fst L · fst ε)
    strict = +Mono< _ _ _ _
      (·MonoR< (abs (x - y)) (fst ε) (fst Bⁿ)
        (snd Bⁿ) x≈y)
      (·MonoL<
        (abs (powℚ n x - powℚ n y))
        (fst L · fst ε) (fst B) (snd B) previous≈)

    factor :
      fst ε · fst Bⁿ + fst B · (fst L · fst ε) ≡
      fst ((powerLipschitzConstant B (suc n)) ·₊ ε)
    factor =
      cong₂ _+_ (ℚ.·Comm (fst ε) (fst Bⁿ))
        (ℚ.·Assoc (fst B) (fst L) (fst ε))
      ∙ sym (ℚ.·DistR+
        (fst Bⁿ) (fst B · fst L) (fst ε))


powerℚ-locallyLipschitz : ∀ n →
  Local.LL.IsLocallyLipschitz (powℚ n)
powerℚ-locallyLipschitz n B =
  powerLipschitzConstant B n , powerℚ-lipschitzOnBall n B


powerℚ-locallyUniformlyContinuous : ∀ n →
  Local.IsLocallyUniformlyContinuous (powℚ n)
powerℚ-locallyUniformlyContinuous n =
  Local.merelyLocallyLipschitz→locallyUniformlyContinuous (powℚ n)
    (λ B → ∣ powerℚ-locallyLipschitz n B ∣₁)


-- The candidate output is now created solely by the generic completion lift
-- from the preceding rational estimate.  This is the missing totality datum
-- in the exact pointwise condition.

powerRestriction : ℕ → ℚ → S.ℭ̂ₛ
powerRestriction n = S.ι ∘ powℚ n


powerRestriction-pointwiseCentered : ∀ n →
  E.P.IsPointwiseCompletionCenteredContinuous (powerRestriction n)
powerRestriction-pointwiseCentered n =
  E.P.bundled→pointwise
    (Local.locallyUniformlyContinuous→completionCenteredContinuous
      (powℚ n) (powerℚ-locallyUniformlyContinuous n))


rationalEstimatePower : ℕ → S.ℭ̂ₛ → S.ℭ̂ₛ
rationalEstimatePower n =
  Local.liftLocallyUniformlyContinuous (powℚ n)
    (powerℚ-locallyUniformlyContinuous n)


rationalEstimatePower-joint : ∀ n x →
  E.C.JointlyApproximableFor (powerRestriction n) x
    (rationalEstimatePower n x)
rationalEstimatePower-joint n =
  Local.liftLocallyUniformlyContinuous-joint (powℚ n)
    (powerℚ-locallyUniformlyContinuous n)


powerRestriction-tendsToRationalEstimatePower : ∀ n x →
  E.TendsToAt (powerRestriction n) x (rationalEstimatePower n x)
powerRestriction-tendsToRationalEstimatePower n x =
  E.pointwiseJoint→tendsToAt
    (powerRestriction-pointwiseCentered n)
    (rationalEstimatePower-joint n x)


powerRestriction-everywhereConvergent : ∀ n →
  Exact.IsEverywhereConvergentRational (powerRestriction n)
powerRestriction-everywhereConvergent n x =
  ∣ rationalEstimatePower n x
  , powerRestriction-tendsToRationalEstimatePower n x
  ∣₁


liftPowerFromEverywhereConvergent :
  ℕ → S.ℭ̂ₛ → S.ℭ̂ₛ
liftPowerFromEverywhereConvergent n =
  Exact.liftEverywhereConvergentRational (powerRestriction n)
    (powerRestriction-everywhereConvergent n)


liftPowerFromEverywhereConvergent-ι : ∀ n q →
  liftPowerFromEverywhereConvergent n (S.ι q) ≡
    S.ι (powℚ n q)
liftPowerFromEverywhereConvergent-ι n =
  E.liftPointwiseContinuousRestriction-ι
    (powerRestriction n)
    (E.everywhereConvergent→pointwiseContinuousRestriction
      (powerRestriction-everywhereConvergent n))


-- Thus the exact-condition lift does not introduce a second power
-- operation: uniqueness of the completed rational graph identifies it with
-- the lift constructed directly from the rational bounded-ball estimate.

liftPowerFromEverywhereConvergent-agreesWithRationalEstimate : ∀ n →
  liftPowerFromEverywhereConvergent n ≡ rationalEstimatePower n
liftPowerFromEverywhereConvergent-agreesWithRationalEstimate n =
  funExt λ x →
    E.jointlyApproximable-unique
      (powerRestriction-pointwiseCentered n) x
      (liftPowerFromEverywhereConvergent n x)
      (rationalEstimatePower n x)
      (E.liftPointwiseContinuousRestriction-joint
        (powerRestriction n)
        (E.everywhereConvergent→pointwiseContinuousRestriction
          (powerRestriction-everywhereConvergent n)) x)
      (rationalEstimatePower-joint n x)
