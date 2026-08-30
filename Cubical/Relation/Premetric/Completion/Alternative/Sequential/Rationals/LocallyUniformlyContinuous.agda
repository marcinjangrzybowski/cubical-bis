module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.LocallyUniformlyContinuous where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.Ring

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals
open import Cubical.Relation.Premetric.Instances.Subspace

open import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.LocallyUniformlyContinuous.Lift public

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingTheory ℚOrderedCommRing
open IsUniformlyContinuousOnBallWith

private
  module Pℚ = PremetricStr (ℚPremetricSpace .snd)

-- Local Lipschitz data is a convenient sufficient source of bounded-ball
-- moduli.  This makes the new lifting theorem immediately applicable to the
-- nonlinear examples already developed for the alternative completion.

locallyLipschitzOnBall→locallyUniformlyContinuousOnBall :
  (f : ℚ → ℚ) (B L : ℚ₊) →
  LL.IsLipschitzOnBallWith f B L →
  IsUniformlyContinuousOnBallWith f B (λ ε → ε ₊／₊ L)
locallyLipschitzOnBall→locallyUniformlyContinuousOnBall f B L lip =
  record
    { pres≈ = λ x y ε absx≤B absy≤B →
        Pℚ.subst≈ (f x) (f y)
          {ε = L ·₊ (ε ₊／₊ L)} {ε' = ε} (·／ L ε) ∘
          lip .LL.IsLipschitzOnBallWith.pres≈
            x y (ε ₊／₊ L) absx≤B absy≤B
    }

IsMerelyLocallyLipschitz : (ℚ → ℚ) → Type₀
IsMerelyLocallyLipschitz f = ∀ B →
  ∃[ L ∈ ℚ₊ ] LL.IsLipschitzOnBallWith f B L

merelyLocallyLipschitz→locallyUniformlyContinuous : ∀ f →
  IsMerelyLocallyLipschitz f → IsLocallyUniformlyContinuous f
merelyLocallyLipschitz→locallyUniformlyContinuous f f-local B =
  PT.map
    (λ { (L , lip) → (λ ε → ε ₊／₊ L) ,
      locallyLipschitzOnBall→locallyUniformlyContinuousOnBall f B L lip })
    (f-local B)


signedSquareℚ-locallyUniformlyContinuous :
  IsLocallyUniformlyContinuous signedSquareℚ
signedSquareℚ-locallyUniformlyContinuous =
  merelyLocallyLipschitz→locallyUniformlyContinuous signedSquareℚ
    (λ B → ∣ LL.signedSquareℚ-locallyLipschitz B ∣₁)

liftSignedSquare : S.ℭ̂ₛ → S.ℭ̂ₛ
liftSignedSquare = liftLocallyUniformlyContinuous signedSquareℚ
  signedSquareℚ-locallyUniformlyContinuous

liftSignedSquare-ι : ∀ q →
  liftSignedSquare (S.ι q) ≡ S.ι (signedSquareℚ q)
liftSignedSquare-ι =
  liftLocallyUniformlyContinuous-ι signedSquareℚ
    signedSquareℚ-locallyUniformlyContinuous

liftSignedSquare-isContinuous : isContinuous
  (SP.ℭ̂ₛPremetricSpace .snd) liftSignedSquare
  (SP.ℭ̂ₛPremetricSpace .snd)
liftSignedSquare-isContinuous =
  liftLocallyUniformlyContinuous-isContinuous signedSquareℚ
    signedSquareℚ-locallyUniformlyContinuous

signedSquareℚ-notUniformlyContinuous :
  isUniformlyContinuous
    (ℚPremetricSpace .snd) signedSquareℚ (ℚPremetricSpace .snd) → ⊥
signedSquareℚ-notUniformlyContinuous f-uc =
  PT.rec isProp⊥
    (λ { (μ , uc) →
      LL.signedSquareℚ-notUniformlyContinuousWith μ uc })
    f-uc


-- Closed-ball presentation of the complete lifting interface.

liftUniformlyContinuousOnClosedBalls : (f : ℚ → ℚ) →
  IsUniformlyContinuousOnClosedBalls f → S.ℭ̂ₛ → S.ℭ̂ₛ
liftUniformlyContinuousOnClosedBalls f closed =
  liftLocallyUniformlyContinuous f
    (onClosedBalls→locallyUniformlyContinuous f closed)

liftUniformlyContinuousOnClosedBalls-joint : ∀ f closed x →
  U.JointlyApproximableFor f x
    (liftUniformlyContinuousOnClosedBalls f closed x)
liftUniformlyContinuousOnClosedBalls-joint f closed =
  liftLocallyUniformlyContinuous-joint f
    (onClosedBalls→locallyUniformlyContinuous f closed)

liftUniformlyContinuousOnClosedBalls-ι : ∀ f closed q →
  liftUniformlyContinuousOnClosedBalls f closed (S.ι q) ≡ S.ι (f q)
liftUniformlyContinuousOnClosedBalls-ι f closed =
  liftLocallyUniformlyContinuous-ι f
    (onClosedBalls→locallyUniformlyContinuous f closed)

liftUniformlyContinuousOnClosedBalls-ext :
  ∀ (f g : ℚ → ℚ)
    (f-closed : IsUniformlyContinuousOnClosedBalls f)
    (g-closed : IsUniformlyContinuousOnClosedBalls g) →
  (∀ q → f q ≡ g q) →
  liftUniformlyContinuousOnClosedBalls f f-closed ≡
    liftUniformlyContinuousOnClosedBalls g g-closed
liftUniformlyContinuousOnClosedBalls-ext
  f g f-closed g-closed f∼g =
  liftLocallyUniformlyContinuous-ext f g
    (onClosedBalls→locallyUniformlyContinuous f f-closed)
    (onClosedBalls→locallyUniformlyContinuous g g-closed)
    f∼g

liftUniformlyContinuousOnClosedBalls-isContinuous : ∀ f closed →
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd)
    (liftUniformlyContinuousOnClosedBalls f closed)
    (SP.ℭ̂ₛPremetricSpace .snd)
liftUniformlyContinuousOnClosedBalls-isContinuous f closed =
  liftLocallyUniformlyContinuous-isContinuous f
    (onClosedBalls→locallyUniformlyContinuous f closed)
