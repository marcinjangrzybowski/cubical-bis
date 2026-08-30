module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.LocallyUniformlyContinuous.Technical where

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

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.UniformlyContinuous
  as UniformDefinition
import Cubical.Relation.Premetric.Completion.Alternative.LiftRationals
  as ExistingLocalLipschitz

module S = SequentialDefinition ℚPremetricSpace
module SP = SequentialPropertiesDefinition ℚPremetricSpace
module U = UniformDefinition ℚPremetricSpace ℚPremetricSpace
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

open import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.ClosedBalls public
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
