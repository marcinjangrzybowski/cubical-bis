module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (_<ℝ_ ; <ℝ-weaken)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius


-- Continuity on a closed ball controls every strict interior point of an
-- agreeing ambient extension.  The domain neighbourhood and the continuity
-- neighbourhood remain separately truncated and are combined only at the
-- requested output radius.

closedAbsRadiusContinuousAtInteriorWithExtension :
  ∀ radius
    (relative-function : ClosedAbsRadius radius → Real.ℝ)
    (function : Real.ℝ → Real.ℝ) →
  isContinuous
    (snd (ClosedAbsRadiusPremetricSpace radius))
    relative-function
    (snd Real.ℝPremetricSpace) →
  (∀ point →
    function (fst point) ≡ relative-function point) →
  ∀ x →
  (interior : Abs.absℝ x <ℝ radius) →
  IsContinuousAt
    (snd Real.ℝPremetricSpace) function
    (snd Real.ℝPremetricSpace) x
closedAbsRadiusContinuousAtInteriorWithExtension
  radius relative-function function relative-continuous agrees
  x interior .IsContinuousAt.pres≈ ε =
  PT.map2 combine
    (relative-continuous centre .IsContinuousAt.pres≈ ε)
    (openAbsRadiusIsOpen radius x interior)
  where
  centre : ClosedAbsRadius radius
  centre = x , <ℝ-weaken (Abs.absℝ x) radius interior

  combine :
    (Σ[ continuity-radius ∈ ℚ₊ ]
      (∀ point →
        x Real.Base.≈ᶜ[ continuity-radius ] fst point →
        relative-function centre Real.Base.≈ᶜ[ ε ]
          relative-function point)) →
    (Σ[ domain-radius ∈ ℚ₊ ]
      (∀ y → x Real.Base.≈ᶜ[ domain-radius ] y →
        Abs.absℝ y <ℝ radius)) →
    Σ[ δ ∈ ℚ₊ ]
      (∀ y → x Real.Base.≈ᶜ[ δ ] y →
        function x Real.Base.≈ᶜ[ ε ] function y)
  combine
    (continuity-radius , relative-close)
    (domain-radius , stays-in-domain) =
    min₊ continuity-radius domain-radius , finish
    where
    finish : ∀ y →
      x Real.Base.≈ᶜ[ min₊ continuity-radius domain-radius ] y →
      function x Real.Base.≈ᶜ[ ε ] function y
    finish y x≈y =
      subst2 (Real.Base._≈ᶜ[ ε ]_)
        (sym (agrees centre))
        (sym (agrees point))
        (relative-close point continuity-close)
      where
      continuity-close :
        x Real.Base.≈ᶜ[ continuity-radius ] y
      continuity-close =
        PremetricStr.isMonotone≈≤
          (snd Real.ℝPremetricSpace)
          x y
          (min₊ continuity-radius domain-radius)
          continuity-radius
          (min₊≤L continuity-radius domain-radius)
          x≈y

      domain-close :
        x Real.Base.≈ᶜ[ domain-radius ] y
      domain-close =
        PremetricStr.isMonotone≈≤
          (snd Real.ℝPremetricSpace)
          x y
          (min₊ continuity-radius domain-radius)
          domain-radius
          (min₊≤R continuity-radius domain-radius)
          x≈y

      point : ClosedAbsRadius radius
      point = y , <ℝ-weaken
        (Abs.absℝ y) radius (stays-in-domain y domain-close)


closedAbsRadiusContinuousAtInterior :
  ∀ radius (function : Real.ℝ → Real.ℝ) →
  isContinuous
    (snd (ClosedAbsRadiusPremetricSpace radius))
    (function ∘ fst)
    (snd Real.ℝPremetricSpace) →
  ∀ x →
  Abs.absℝ x <ℝ radius →
  IsContinuousAt
    (snd Real.ℝPremetricSpace) function
    (snd Real.ℝPremetricSpace) x
closedAbsRadiusContinuousAtInterior
  radius function relative-continuous =
  closedAbsRadiusContinuousAtInteriorWithExtension
    radius (function ∘ fst) function
    relative-continuous (λ _ → refl)
