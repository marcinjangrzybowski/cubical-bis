module Cubical.Relation.Premetric.Completion.Rationals.PointwiseContinuousExtension.LocalRepresentatives where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ hiding (isProp∼)

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Base
  as CompletionDefinition
import Cubical.Relation.Premetric.Completion.Properties.Closeness
  as CompletionPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Lift.PointwiseContinuousExtension
  as PointwiseExtensionDefinition

module R = CompletionDefinition ℚPremetricSpace
module RP = CompletionPropertiesDefinition ℚPremetricSpace
module E = PointwiseExtensionDefinition ℚPremetricSpace ℚPremetricSpace

private
  module Pℝ = PremetricStr (RP.ℭPremetricSpace .snd)

open PositiveRationals
open PositiveHalvesℚ


-- A representative is needed only on one neighbourhood of x.  Away from x
-- it may be an arbitrary continuous function, such as a clamped or otherwise
-- bounded lift.

LocalContinuousRepresentativeAt :
  (ℚ → R.ℭ) → R.ℭ → Type₀
LocalContinuousRepresentativeAt f x =
  Σ[ F ∈ (R.ℭ → R.ℭ) ]
    (isContinuous
      (RP.ℭPremetricSpace .snd) F
      (RP.ℭPremetricSpace .snd))
    ×
    (Σ[ ρ ∈ ℚ₊ ]
      (∀ q → R.ι q R.∼[ ρ ] x → F (R.ι q) ≡ f q))


IsMerelyLocallyContinuouslyRepresentable :
  (ℚ → R.ℭ) → Type₀
IsMerelyLocallyContinuouslyRepresentable f =
  ∀ x → ∥ LocalContinuousRepresentativeAt f x ∥₁


localContinuousRepresentative-tends :
  ∀ f x →
  (representative : LocalContinuousRepresentativeAt f x) →
  E.TendsToAt f x (representative .fst x)
localContinuousRepresentative-tends f x (F , F-cont , ρ , agrees) ε =
  PT.map convert (E.continuousRestriction-tends F F-cont x ε)
  where
  convert :
    ( Σ[ δ ∈ ℚ₊ ]
      (∀ q → R.ι q R.∼[ δ ] x →
        F (R.ι q) R.∼[ ε ] F x)) →
    Σ[ θ ∈ ℚ₊ ]
      (∀ q → R.ι q R.∼[ θ ] x →
        f q R.∼[ ε ] F x)
  convert (δ , near) = min₊ δ ρ /2₊ , λ q ιq∼x →
    subst
      (λ z → z R.∼[ ε ] F x)
      (agrees q
        (Pℝ.isMonotone≈< (R.ι q) x (min₊ δ ρ /2₊) ρ
          (min/2₊<R δ ρ) ιq∼x))
      (near q
        (Pℝ.isMonotone≈< (R.ι q) x (min₊ δ ρ /2₊) δ
          (min/2₊<L δ ρ) ιq∼x))


merelyLocallyRepresentable→everywhereConvergent : ∀ f →
  IsMerelyLocallyContinuouslyRepresentable f →
  E.IsEverywhereConvergent f
merelyLocallyRepresentable→everywhereConvergent f local x =
  PT.map
    (λ representative →
      representative .fst x ,
      localContinuousRepresentative-tends f x representative)
    (local x)


liftMerelyLocallyRepresentable :
  (f : ℚ → R.ℭ) →
  IsMerelyLocallyContinuouslyRepresentable f →
  R.ℭ → R.ℭ
liftMerelyLocallyRepresentable f local =
  E.liftEverywhereConvergent f
    (merelyLocallyRepresentable→everywhereConvergent f local)


liftMerelyLocallyRepresentable-ι :
  ∀ f local q →
  liftMerelyLocallyRepresentable f local (R.ι q) ≡ f q
liftMerelyLocallyRepresentable-ι f local =
  E.liftEverywhereConvergent-ι f
    (merelyLocallyRepresentable→everywhereConvergent f local)


liftMerelyLocallyRepresentable-isContinuous :
  ∀ f local →
  isContinuous
    (RP.ℭPremetricSpace .snd)
    (liftMerelyLocallyRepresentable f local)
    (RP.ℭPremetricSpace .snd)
liftMerelyLocallyRepresentable-isContinuous f local =
  E.liftEverywhereConvergent-isContinuous f
    (merelyLocallyRepresentable→everywhereConvergent f local)
