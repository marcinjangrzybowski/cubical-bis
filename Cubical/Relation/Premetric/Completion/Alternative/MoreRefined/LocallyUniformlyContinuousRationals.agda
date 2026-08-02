module Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.LocallyUniformlyContinuousRationals where

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

import Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.Base
  as MoreRefinedDefinition
import Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.Properties
  as MoreRefinedPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.UniformlyContinuousRationals
  as UniformDefinition
import Cubical.Relation.Premetric.Completion.Alternative.LiftRationals
  as ExistingLocalLipschitz

module S = MoreRefinedDefinition ℚPremetricSpace
module SP = MoreRefinedPropertiesDefinition ℚPremetricSpace
module U = UniformDefinition
module LL = ExistingLocalLipschitz

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing

private
  module Pℚ = PremetricStr (ℚPremetricSpace .snd)
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


-- This is deliberately a bounded-ball condition, not global uniform
-- continuity.  The modulus may depend on the ball, and its existence is
-- truncated so that no global choice of moduli is required.

record IsUniformlyContinuousOnBallWith
  (f : ℚ → ℚ) (B : ℚ₊) (μ : ℚ₊ → ℚ₊) : Type₀ where
  no-eta-equality
  field
    pres≈ : ∀ x y ε
      → abs x ≤ℚ fst B
      → abs y ≤ℚ fst B
      → x Pℚ.≈[ μ ε ] y
      → f x Pℚ.≈[ ε ] f y

open IsUniformlyContinuousOnBallWith

IsLocallyUniformlyContinuous : (ℚ → ℚ) → Type₀
IsLocallyUniformlyContinuous f = ∀ B →
  ∃[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousOnBallWith f B μ

isPropIsLocallyUniformlyContinuous : ∀ f →
  isProp (IsLocallyUniformlyContinuous f)
isPropIsLocallyUniformlyContinuous f = isPropΠ λ _ → squash₁


-- The same condition, presented intrinsically on the rational closed-ball
-- subspace rather than by passing the two membership proofs as arguments.

ClosedBallℚPredicate : ℚ₊ → ℙ ℚ
ClosedBallℚPredicate B q =
  (abs q ≤ℚ fst B) , ℚ.isProp≤ (abs q) (fst B)

ClosedBallℚPremetricSpace : ℚ₊ → PremetricSpace ℓ-zero ℓ-zero
ClosedBallℚPremetricSpace B =
  PremetricSubspace ℚPremetricSpace (ClosedBallℚPredicate B)

ClosedBallℚ : ℚ₊ → Type₀
ClosedBallℚ B = ⟨ ClosedBallℚPremetricSpace B ⟩

IsUniformlyContinuousOnClosedBallWith :
  (ℚ → ℚ) → ℚ₊ → (ℚ₊ → ℚ₊) → Type₀
IsUniformlyContinuousOnClosedBallWith f B μ =
  IsUniformlyContinuousWith
    (ClosedBallℚPremetricSpace B .snd) (f ∘ fst)
    (ℚPremetricSpace .snd) μ

onBallWith→onClosedBallWith : ∀ f B μ →
  IsUniformlyContinuousOnBallWith f B μ →
  IsUniformlyContinuousOnClosedBallWith f B μ
onBallWith→onClosedBallWith f B μ local
  .IsUniformlyContinuousWith.pres≈ x y ε x≈y =
  local .pres≈ (fst x) (fst y) ε (snd x) (snd y) x≈y

onClosedBallWith→onBallWith : ∀ f B μ →
  IsUniformlyContinuousOnClosedBallWith f B μ →
  IsUniformlyContinuousOnBallWith f B μ
onClosedBallWith→onBallWith f B μ local .pres≈
  x y ε absx≤B absy≤B x≈y =
  local .IsUniformlyContinuousWith.pres≈
    (x , absx≤B) (y , absy≤B) ε x≈y

IsUniformlyContinuousOnClosedBalls : (ℚ → ℚ) → Type₀
IsUniformlyContinuousOnClosedBalls f = ∀ B →
  ∃[ μ ∈ (ℚ₊ → ℚ₊) ]
    IsUniformlyContinuousOnClosedBallWith f B μ

isPropIsUniformlyContinuousOnClosedBalls : ∀ f →
  isProp (IsUniformlyContinuousOnClosedBalls f)
isPropIsUniformlyContinuousOnClosedBalls f = isPropΠ λ _ → squash₁

onClosedBalls→locallyUniformlyContinuous : ∀ f →
  IsUniformlyContinuousOnClosedBalls f →
  IsLocallyUniformlyContinuous f
onClosedBalls→locallyUniformlyContinuous f closed B =
  PT.map
    (λ { (μ , uc) → μ , onClosedBallWith→onBallWith f B μ uc })
    (closed B)

locallyUniformlyContinuous→onClosedBalls : ∀ f →
  IsLocallyUniformlyContinuous f →
  IsUniformlyContinuousOnClosedBalls f
locallyUniformlyContinuous→onClosedBalls f local B =
  PT.map
    (λ { (μ , uc) → μ , onBallWith→onClosedBallWith f B μ uc })
    (local B)

locallyUniformlyContinuous≃onClosedBalls : ∀ f →
  IsLocallyUniformlyContinuous f ≃
    IsUniformlyContinuousOnClosedBalls f
locallyUniformlyContinuous≃onClosedBalls f = propBiimpl→Equiv
  (isPropIsLocallyUniformlyContinuous f)
  (isPropIsUniformlyContinuousOnClosedBalls f)
  (locallyUniformlyContinuous→onClosedBalls f)
  (onClosedBalls→locallyUniformlyContinuous f)


-- Clamping to [-B,B] is non-expanding.  It turns one local modulus on B
-- into a global modulus for the clamped function.

clampBall : ℚ₊ → ℚ → ℚ
clampBall B = ℚ.clamp (ℚ.- fst B) (fst B)

clampBall-bounded : ∀ B q → abs (clampBall B q) ≤ℚ fst B
clampBall-bounded B q = ℚ.absFrom≤×≤ (fst B) (clampBall B q)
  (ℚ.≤clamp (ℚ.- fst B) (fst B) q
    (ℚ.isTrans≤ (ℚ.- fst B) 0 (fst B)
      (ℚ.-ℚ₊≤0 B) (ℚ.0≤ℚ₊ B)))
  (ℚ.clamp≤ (ℚ.- fst B) (fst B) q)

clampBall-pres≈ : ∀ B x y ε →
  x Pℚ.≈[ ε ] y → clampBall B x Pℚ.≈[ ε ] clampBall B y
clampBall-pres≈ B x y ε x≈y = ℚ.isTrans≤<
  (abs (clampBall B x ℚ.- clampBall B y))
  (abs (x ℚ.- y)) (fst ε)
  (ℚ.clampDist (ℚ.- fst B) (fst B) y x) x≈y

absToBounds : ∀ (B : ℚ₊) q → abs q ≤ℚ fst B →
  (ℚ.- fst B ≤ℚ q) × (q ≤ℚ fst B)
absToBounds B q absq≤B .fst =
  subst (ℚ.- fst B ≤ℚ_) (ℚ.-Invol q)
    (ℚ.minus-≤ (ℚ.- q) (fst B)
      (ℚ.isTrans≤ (ℚ.- q) (abs q) (fst B)
        (OrderedCommRingTheory.-≤abs ℚOrderedCommRing q) absq≤B))
absToBounds B q absq≤B .snd =
  ℚ.isTrans≤ q (abs q) (fst B)
    (OrderedCommRingTheory.≤abs ℚOrderedCommRing q) absq≤B

clampBall-fixes : ∀ B q → abs q ≤ℚ fst B → clampBall B q ≡ q
clampBall-fixes B q absq≤B =
  ℚ.inClamps (ℚ.- fst B) (fst B) q lowerBound upperBound
  where
  bounds : (ℚ.- fst B ≤ℚ q) × (q ≤ℚ fst B)
  bounds = absToBounds B q absq≤B

  lowerBound : ℚ.- fst B ≤ℚ q
  lowerBound = bounds .fst

  upperBound : q ≤ℚ fst B
  upperBound = bounds .snd


clamped-isUniformlyContinuousWith : ∀ f B μ →
  IsUniformlyContinuousOnBallWith f B μ →
  IsUniformlyContinuousWith
    (ℚPremetricSpace .snd) (f ∘ clampBall B)
    (ℚPremetricSpace .snd) μ
clamped-isUniformlyContinuousWith f B μ local
  .IsUniformlyContinuousWith.pres≈ x y ε x≈y =
  local .pres≈ (clampBall B x) (clampBall B y) ε
    (clampBall-bounded B x) (clampBall-bounded B y)
    (clampBall-pres≈ B x y (μ ε) x≈y)


-- A single rational approximation to x bounds all sufficiently accurate
-- rational approximations to x.  The generous constant 2 + max(1,|a|)
-- keeps the proof independent of non-strict boundary choices.

anchorBound : ℚ → ℚ₊
anchorBound a = (1 +₊ 1) +₊ ℚ.maxWithPos 1 (abs a)

closeToAnchor-bounded : ∀ a q →
  q Pℚ.≈[ 1 +₊ 1 ] a → abs q ≤ℚ fst (anchorBound a)
closeToAnchor-bounded a q q≈a = begin≤
  abs q
    ≡→≤⟨ sym (cong abs
      (cong (q ℚ.+_) ℚRing.0Selfinverse ∙ ℚ.+IdR q)) ⟩
  abs (q ℚ.- 0)
    ≤⟨ triangularInequality- q 0 a ⟩
  abs (q ℚ.- a) ℚ.+ abs (a ℚ.- 0)
    ≡→≤⟨ cong (abs (q ℚ.- a) ℚ.+_)
      (cong abs
        (cong (a ℚ.+_) ℚRing.0Selfinverse ∙ ℚ.+IdR a)) ⟩
  abs (q ℚ.- a) ℚ.+ abs a
    <⟨ +MonoR< _ _ (abs a) q≈a ⟩
  fst (1 +₊ 1) ℚ.+ abs a
    ≤⟨ +MonoL≤ (abs a) (fst (ℚ.maxWithPos 1 (abs a)))
      (fst (1 +₊ 1)) (ℚ.≤max' 1 (abs a)) ⟩
  fst (anchorBound a) ◾

approximation-bounded : ∀ a x q δ →
  S.ι a S.∼̂ₛ[ 1 ] x →
  δ <₊ 1 →
  S.ι q S.∼̂ₛ[ δ ] x →
  abs q ≤ℚ fst (anchorBound a)
approximation-bounded a x q δ ιa∼x δ<1 ιq∼x =
  closeToAnchor-bounded a q
    (U.ι-ι-reflects∼ q a (1 +₊ 1)
      (S.isMonotone∼̂ₛ< (S.ι q) (S.ι a) (δ +₊ 1) (1 +₊ 1)
        (+MonoR< (fst δ) 1 1 δ<1)
        (S.tri∼ (S.ι q) x (S.ι a) δ 1
          ιq∼x (S.sym∼ (S.ι a) x 1 ιa∼x))))


private
  witnessRadius : ℚ₊ → ℚ₊
  witnessRadius α = min₊ α 1 /2₊

jointlyApproximable-toClamped : ∀ f a x y →
  S.ι a S.∼̂ₛ[ 1 ] x →
  U.JointlyApproximableFor f x y →
  U.JointlyApproximableFor (f ∘ clampBall (anchorBound a)) x y
jointlyApproximable-toClamped f a x y ιa∼x joint α β =
  PT.map convert (joint (witnessRadius α) β)
  where
  δ = witnessRadius α
  B = anchorBound a

  convert :
    ( Σ[ q ∈ ℚ ]
      (S.ι q S.∼̂ₛ[ δ ] x) ×
      (S.ι (f q) S.∼̂ₛ[ β ] y)) →
    Σ[ q ∈ ℚ ]
      (S.ι q S.∼̂ₛ[ α ] x) ×
      (S.ι ((f ∘ clampBall B) q) S.∼̂ₛ[ β ] y)
  convert (q , ιq∼x , ιfq∼y) = q ,
    S.isMonotone∼̂ₛ< (S.ι q) x δ α
      (min/2₊<L α 1) ιq∼x ,
    subst (λ z → S.ι z S.∼̂ₛ[ β ] y)
      (sym (cong f clamp-fixes-q)) ιfq∼y
    where
    q-bounded : abs q ≤ℚ fst B
    q-bounded = approximation-bounded a x q δ ιa∼x
      (min/2₊<R α 1) ιq∼x

    clamp-fixes-q : clampBall B q ≡ q
    clamp-fixes-q = clampBall-fixes B q q-bounded


jointlyApproximable-fromClamped : ∀ f a x y →
  S.ι a S.∼̂ₛ[ 1 ] x →
  U.JointlyApproximableFor (f ∘ clampBall (anchorBound a)) x y →
  U.JointlyApproximableFor f x y
jointlyApproximable-fromClamped f a x y ιa∼x joint α β =
  PT.map convert (joint (witnessRadius α) β)
  where
  δ = witnessRadius α
  B = anchorBound a

  convert :
    ( Σ[ q ∈ ℚ ]
      (S.ι q S.∼̂ₛ[ δ ] x) ×
      (S.ι ((f ∘ clampBall B) q) S.∼̂ₛ[ β ] y)) →
    Σ[ q ∈ ℚ ]
      (S.ι q S.∼̂ₛ[ α ] x) ×
      (S.ι (f q) S.∼̂ₛ[ β ] y)
  convert (q , ιq∼x , ιfclampq∼y) = q ,
    S.isMonotone∼̂ₛ< (S.ι q) x δ α
      (min/2₊<L α 1) ιq∼x ,
    subst (λ z → S.ι z S.∼̂ₛ[ β ] y)
      (cong f clamp-fixes-q) ιfclampq∼y
    where
    q-bounded : abs q ≤ℚ fst B
    q-bounded = approximation-bounded a x q δ ιa∼x
      (min/2₊<R α 1) ιq∼x

    clamp-fixes-q : clampBall B q ≡ q
    clamp-fixes-q = clampBall-fixes B q q-bounded


jointlyApproximable-equal : ∀ f →
  IsLocallyUniformlyContinuous f →
  ∀ x y y' →
  U.JointlyApproximableFor f x y →
  U.JointlyApproximableFor f x y' →
  y ≡ y'
jointlyApproximable-equal f f-luc x y y' xy xy' =
  PT.rec (S.isSetℭ̂ₛ y y') withAnchor (SP.∃approx x 1)
  where
  withAnchor :
    (Σ[ a ∈ ℚ ] (S.ι a S.∼̂ₛ[ 1 ] x)) → y ≡ y'
  withAnchor (a , ιa∼x) =
    PT.rec (S.isSetℭ̂ₛ y y') withLocalData (f-luc B)
    where
    B = anchorBound a

    withLocalData :
      (Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
        IsUniformlyContinuousOnBallWith f B μ) → y ≡ y'
    withLocalData (μ , local) =
      U.WithModulus.jointlyApproximable-equal
        (f ∘ clampBall B) μ
        (clamped-isUniformlyContinuousWith f B μ local)
        x y y'
        (jointlyApproximable-toClamped f a x y ιa∼x xy)
        (jointlyApproximable-toClamped f a x y' ιa∼x xy')


LiftFiber : (ℚ → ℚ) → S.ℭ̂ₛ → Type₀
LiftFiber f x = Σ[ y ∈ S.ℭ̂ₛ ] U.JointlyApproximableFor f x y

isPropLiftFiber : ∀ f →
  IsLocallyUniformlyContinuous f → ∀ x → isProp (LiftFiber f x)
isPropLiftFiber f f-luc x (y , xy) (y' , xy') =
  Σ≡Prop (U.isPropJointlyApproximableFor f x)
    (jointlyApproximable-equal f f-luc x y y' xy xy')


private
  fiberFromAnchorAndLocalData : ∀ f x a →
    (anchor : S.ι a S.∼̂ₛ[ 1 ] x) →
    (d : Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
      IsUniformlyContinuousOnBallWith f (anchorBound a) μ) →
    LiftFiber f x
  fiberFromAnchorAndLocalData f x a anchor (μ , local) =
    y , jointlyApproximable-fromClamped f a x y anchor clipped-joint
    where
    B = anchorBound a
    clipped = f ∘ clampBall B
    clipped-uc = clamped-isUniformlyContinuousWith f B μ local

    y : S.ℭ̂ₛ
    y = U.WithModulus.liftUniformlyContinuousWith
      clipped μ clipped-uc x

    clipped-joint : U.JointlyApproximableFor clipped x y
    clipped-joint =
      U.WithModulus.liftUniformlyContinuousWith-joint
        clipped μ clipped-uc x


liftFiber : ∀ f →
  IsLocallyUniformlyContinuous f → ∀ x → LiftFiber f x
liftFiber f f-luc x =
  PT.rec (isPropLiftFiber f f-luc x) withAnchor (SP.∃approx x 1)
  where
  withAnchor :
    (Σ[ a ∈ ℚ ] (S.ι a S.∼̂ₛ[ 1 ] x)) → LiftFiber f x
  withAnchor (a , anchor) =
    PT.rec (isPropLiftFiber f f-luc x)
      (fiberFromAnchorAndLocalData f x a anchor)
      (f-luc (anchorBound a))


liftLocallyUniformlyContinuous : (f : ℚ → ℚ) →
  IsLocallyUniformlyContinuous f → S.ℭ̂ₛ → S.ℭ̂ₛ
liftLocallyUniformlyContinuous f f-luc x = liftFiber f f-luc x .fst

liftLocallyUniformlyContinuous-joint : ∀ f f-luc x →
  U.JointlyApproximableFor f x
    (liftLocallyUniformlyContinuous f f-luc x)
liftLocallyUniformlyContinuous-joint f f-luc x =
  liftFiber f f-luc x .snd

liftLocallyUniformlyContinuous-ι : ∀ f f-luc q →
  liftLocallyUniformlyContinuous f f-luc (S.ι q) ≡ S.ι (f q)
liftLocallyUniformlyContinuous-ι f f-luc q =
  cong fst (isPropLiftFiber f f-luc (S.ι q)
    (liftFiber f f-luc (S.ι q)) baseFiber)
  where
  baseFiber : LiftFiber f (S.ι q)
  baseFiber .fst = S.ι (f q)
  baseFiber .snd α β =
    ∣ q , S.isRefl∼̂ₛ (S.ι q) α
        , S.isRefl∼̂ₛ (S.ι (f q)) β ∣₁


-- Global uniform continuity is a special case.  More importantly, local
-- Lipschitz bounds imply the new hypothesis, so nonlinear examples such as
-- signed squaring now lift to the whole completion.

uniformlyContinuous→locallyUniformlyContinuous : ∀ f →
  isUniformlyContinuous
    (ℚPremetricSpace .snd) f (ℚPremetricSpace .snd) →
  IsLocallyUniformlyContinuous f
uniformlyContinuous→locallyUniformlyContinuous f f-uc B =
  PT.map makeLocal f-uc
  where
  makeLocal : U.UniformContinuityData f →
    Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousOnBallWith f B μ
  makeLocal (μ , uc) = μ , local
    where
    local : IsUniformlyContinuousOnBallWith f B μ
    local .pres≈ x y ε _ _ =
      uc .IsUniformlyContinuousWith.pres≈ x y ε


liftLocallyUniformlyContinuous-agreesWithUniformlyContinuousWith :
  ∀ f f-luc μ
  (f-uc : IsUniformlyContinuousWith
    (ℚPremetricSpace .snd) f (ℚPremetricSpace .snd) μ) →
  liftLocallyUniformlyContinuous f f-luc ≡
    U.WithModulus.liftUniformlyContinuousWith f μ f-uc
liftLocallyUniformlyContinuous-agreesWithUniformlyContinuousWith
  f f-luc μ f-uc = funExt λ x →
    jointlyApproximable-equal f f-luc x _ _
      (liftLocallyUniformlyContinuous-joint f f-luc x)
      (U.WithModulus.liftUniformlyContinuousWith-joint f μ f-uc x)


private
  one₊ : ℚ₊
  one₊ = 1

  quarter : ℚ₊
  quarter = one₊ /4₊

  quarterPlusSmall<one : ∀ δ → δ <₊ quarter →
    (quarter +₊ δ) <₊ one₊
  quarterPlusSmall<one δ δ<quarter = begin<
    fst (quarter +₊ δ)
      <⟨ +MonoL< (fst δ) (fst quarter) (fst quarter) δ<quarter ⟩
    fst (quarter +₊ quarter)
      ≡→≤⟨ /4+/4≡/2 (fst one₊) ⟩
    fst (one₊ /2₊)
      <⟨ /2₊<id one₊ ⟩
    fst one₊ ◾

  jointlyApproximable-equalClamped : ∀ f a x y μ
    (local : IsUniformlyContinuousOnBallWith f (anchorBound a) μ) →
    S.ι a S.∼̂ₛ[ 1 ] x →
    U.JointlyApproximableFor f x y →
    y ≡ U.WithModulus.liftUniformlyContinuousWith
      (f ∘ clampBall (anchorBound a)) μ
      (clamped-isUniformlyContinuousWith f (anchorBound a) μ local) x
  jointlyApproximable-equalClamped f a x y μ local anchor joint =
    U.WithModulus.jointlyApproximable-equal clipped μ clipped-uc x y Gx
      (jointlyApproximable-toClamped f a x y anchor joint)
      (U.WithModulus.liftUniformlyContinuousWith-joint
        clipped μ clipped-uc x)
    where
    B = anchorBound a
    clipped = f ∘ clampBall B
    clipped-uc = clamped-isUniformlyContinuousWith f B μ local
    Gx = U.WithModulus.liftUniformlyContinuousWith clipped μ clipped-uc x


liftLocallyUniformlyContinuous-isContinuous : ∀ f
  (f-luc : IsLocallyUniformlyContinuous f) →
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd)
    (liftLocallyUniformlyContinuous f f-luc)
    (SP.ℭ̂ₛPremetricSpace .snd)
liftLocallyUniformlyContinuous-isContinuous f f-luc x
  .IsContinuousAt.pres≈ ε =
  PT.rec squash₁ withAnchor (SP.∃approx x quarter)
  where
  F = liftLocallyUniformlyContinuous f f-luc

  withAnchor :
    (Σ[ a ∈ ℚ ] (S.ι a S.∼̂ₛ[ quarter ] x)) →
    ∃[ δ ∈ ℚ₊ ] (∀ y → x S.∼̂ₛ[ δ ] y → F x S.∼̂ₛ[ ε ] F y)
  withAnchor (a , anchor-small) = PT.map withLocalData (f-luc B)
    where
    B = anchorBound a

    withLocalData :
      (Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
        IsUniformlyContinuousOnBallWith f B μ) →
      Σ[ δ ∈ ℚ₊ ]
        (∀ y → x S.∼̂ₛ[ δ ] y → F x S.∼̂ₛ[ ε ] F y)
    withLocalData (μ , local) = δ , preserve
      where
      clipped = f ∘ clampBall B
      clipped-uc = clamped-isUniformlyContinuousWith f B μ local
      input = U.WithModulus.inputBudget clipped μ clipped-uc ε
      δ = min₊ input quarter /2₊

      anchor-x : S.ι a S.∼̂ₛ[ 1 ] x
      anchor-x = S.isMonotone∼̂ₛ< (S.ι a) x quarter 1
        (/4₊<id one₊) anchor-small

      preserve : ∀ y → x S.∼̂ₛ[ δ ] y → F x S.∼̂ₛ[ ε ] F y
      preserve y x∼y =
        subst2 (S._∼̂ₛ[ ε ]_)
          (sym Fx≡Gx) (sym Fy≡Gy) Gx∼Gy
        where
        anchor-y-small : S.ι a S.∼̂ₛ[ quarter +₊ δ ] y
        anchor-y-small = S.tri∼ (S.ι a) x y quarter δ
          anchor-small x∼y

        anchor-y : S.ι a S.∼̂ₛ[ 1 ] y
        anchor-y = S.isMonotone∼̂ₛ< (S.ι a) y (quarter +₊ δ) 1
          (quarterPlusSmall<one δ (min/2₊<R input quarter))
          anchor-y-small

        Fx≡Gx : F x ≡
          U.WithModulus.liftUniformlyContinuousWith
            clipped μ clipped-uc x
        Fx≡Gx = jointlyApproximable-equalClamped
          f a x (F x) μ local anchor-x
          (liftLocallyUniformlyContinuous-joint f f-luc x)

        Fy≡Gy : F y ≡
          U.WithModulus.liftUniformlyContinuousWith
            clipped μ clipped-uc y
        Fy≡Gy = jointlyApproximable-equalClamped
          f a y (F y) μ local anchor-y
          (liftLocallyUniformlyContinuous-joint f f-luc y)

        x∼y-input : x S.∼̂ₛ[ input ] y
        x∼y-input = S.isMonotone∼̂ₛ< x y δ input
          (min/2₊<L input quarter) x∼y

        Gx∼Gy :
          U.WithModulus.liftUniformlyContinuousWith clipped μ clipped-uc x
          S.∼̂ₛ[ ε ]
          U.WithModulus.liftUniformlyContinuousWith clipped μ clipped-uc y
        Gx∼Gy = U.WithModulus.liftUniformlyContinuousWith-pres∼
          clipped μ clipped-uc x y ε x∼y-input


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

liftUniformlyContinuousOnClosedBalls-isContinuous : ∀ f closed →
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd)
    (liftUniformlyContinuousOnClosedBalls f closed)
    (SP.ℭ̂ₛPremetricSpace .snd)
liftUniformlyContinuousOnClosedBalls-isContinuous f closed =
  liftLocallyUniformlyContinuous-isContinuous f
    (onClosedBalls→locallyUniformlyContinuous f closed)
