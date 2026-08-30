module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.LocallyUniformlyContinuous.Lift where

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

open import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.LocallyUniformlyContinuous.Technical public

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CompletionCentered
  as CompletionCenteredDefinition

module CC = CompletionCenteredDefinition ℚPremetricSpace ℚPremetricSpace

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingTheory ℚOrderedCommRing
open IsUniformlyContinuousOnBallWith

private
  module PS = PremetricStr (SP.ℭ̂ₛPremetricSpace .snd)
  module Pℚ = PremetricStr (ℚPremetricSpace .snd)


locallyUniformlyContinuous→completionCenteredContinuous : ∀ f →
  IsLocallyUniformlyContinuous f →
  CC.IsCompletionCenteredContinuous (S.ι ∘ f)
locallyUniformlyContinuous→completionCenteredContinuous f f-luc
  .CC.IsCompletionCenteredContinuous.at x =
  PT.rec squash₁ withAnchor (SP.∃approx x 1)
  where
  withAnchor :
    (Σ[ a ∈ ℚ ] (S.ι a S.∼̂ₛ[ 1 ] x)) →
    ∃[ ν ∈ (ℚ₊ → ℚ₊) ]
      CC.IsCompletionContinuousAtWith (S.ι ∘ f) x ν
  withAnchor (a , anchor) =
    PT.map withLocalData (f-luc (anchorBound a))
    where
    withLocalData :
      (Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
        IsUniformlyContinuousOnBallWith f (anchorBound a) μ) →
      Σ[ ν ∈ (ℚ₊ → ℚ₊) ]
        CC.IsCompletionContinuousAtWith (S.ι ∘ f) x ν
    withLocalData (μ , local) = ν , centered
      where
      ν : ℚ₊ → ℚ₊
      ν ε = min₊ (μ ε) 1 /2₊

      centered : CC.IsCompletionContinuousAtWith (S.ι ∘ f) x ν
      centered .CC.IsCompletionContinuousAtWith.pres∼
        q r ε ιq∼x ιr∼x =
        S.ι-ι (f q) (f r) ε
          (local .pres≈ q r ε q-bounded r-bounded q≈r)
        where
        q-bounded : abs q ≤ℚ fst (anchorBound a)
        q-bounded = approximation-bounded a x q (ν ε) anchor
          (min/2₊<R (μ ε) 1) ιq∼x

        r-bounded : abs r ≤ℚ fst (anchorBound a)
        r-bounded = approximation-bounded a x r (ν ε) anchor
          (min/2₊<R (μ ε) 1) ιr∼x

        radius≤ : (ν ε +₊ ν ε) ≤₊ μ ε
        radius≤ = subst (_≤ℚ fst (μ ε))
          (sym (/2+/2≡id (fst (min₊ (μ ε) 1))))
          (min₊≤L (μ ε) 1)

        q≈r : q Pℚ.≈[ μ ε ] r
        q≈r = U.ι-ι-reflects∼ q r (μ ε)
          (PS.isMonotone≈≤ (S.ι q) (S.ι r)
            (ν ε +₊ ν ε) (μ ε) radius≤
            (S.tri∼ (S.ι q) x (S.ι r) (ν ε) (ν ε)
              ιq∼x (S.sym∼ (S.ι r) x (ν ε) ιr∼x)))


liftLocallyUniformlyContinuous : (f : ℚ → ℚ) →
  IsLocallyUniformlyContinuous f → S.ℭ̂ₛ → S.ℭ̂ₛ
liftLocallyUniformlyContinuous f f-luc =
  CC.liftCompletionCenteredContinuous (S.ι ∘ f)
    (locallyUniformlyContinuous→completionCenteredContinuous f f-luc)

liftLocallyUniformlyContinuous-joint : ∀ f f-luc x →
  U.JointlyApproximableFor f x
    (liftLocallyUniformlyContinuous f f-luc x)
liftLocallyUniformlyContinuous-joint f f-luc x =
  CC.liftCompletionCenteredContinuous-joint (S.ι ∘ f)
    (locallyUniformlyContinuous→completionCenteredContinuous f f-luc) x

liftLocallyUniformlyContinuous-ι : ∀ f f-luc q →
  liftLocallyUniformlyContinuous f f-luc (S.ι q) ≡ S.ι (f q)
liftLocallyUniformlyContinuous-ι f f-luc =
  CC.liftCompletionCenteredContinuous-ι (S.ι ∘ f)
    (locallyUniformlyContinuous→completionCenteredContinuous f f-luc)

liftLocallyUniformlyContinuous-ext :
  ∀ (f g : ℚ → ℚ)
    (f-luc : IsLocallyUniformlyContinuous f)
    (g-luc : IsLocallyUniformlyContinuous g) →
  (∀ q → f q ≡ g q) →
  liftLocallyUniformlyContinuous f f-luc ≡
    liftLocallyUniformlyContinuous g g-luc
liftLocallyUniformlyContinuous-ext f g f-luc g-luc f∼g =
  CC.liftCompletionCenteredContinuous-ext (S.ι ∘ f) (S.ι ∘ g)
    (locallyUniformlyContinuous→completionCenteredContinuous f f-luc)
    (locallyUniformlyContinuous→completionCenteredContinuous g g-luc)
    (λ q → cong S.ι (f∼g q))


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


liftLocallyUniformlyContinuous-isContinuous : ∀ f
  (f-luc : IsLocallyUniformlyContinuous f) →
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd)
    (liftLocallyUniformlyContinuous f f-luc)
    (SP.ℭ̂ₛPremetricSpace .snd)
liftLocallyUniformlyContinuous-isContinuous f f-luc =
  CC.liftCompletionCenteredContinuous-isContinuous (S.ι ∘ f)
    (locallyUniformlyContinuous→completionCenteredContinuous f f-luc)
