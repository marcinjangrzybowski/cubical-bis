module Cubical.Analysis.Real.UniversalProperty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Analysis.Completion.Extensionality
  as ExtensionalityDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CauchyContinuous
  as CauchyContinuousDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.UniformlyContinuous
  as UniformlyContinuousDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CompletionCentered
  as CompletionCenteredDefinition

module Ext = ExtensionalityDefinition ℚPremetricSpace
module C = CauchyContinuousDefinition ℚPremetricSpace ℚPremetricSpace
module U = UniformlyContinuousDefinition ℚPremetricSpace ℚPremetricSpace
module CC = CompletionCenteredDefinition ℚPremetricSpace ℚPremetricSpace


-- Metric extensionality for the sequence-backed real presentation.

continuousExtensionality :
  (f g : ℝ → ℝ) →
  isContinuous (ℝPremetricSpace .snd) f (ℝPremetricSpace .snd) →
  isContinuous (ℝPremetricSpace .snd) g (ℝPremetricSpace .snd) →
  (∀ q → f (rat q) ≡ g (rat q)) →
  f ≡ g
continuousExtensionality = Ext.continuousExtensionality ℝPremetricSpace

continuousExtensionality₂ :
  (f g : ℝ → ℝ → ℝ) →
  (∀ y → isContinuous (ℝPremetricSpace .snd)
    (λ x → f x y) (ℝPremetricSpace .snd)) →
  (∀ x → isContinuous (ℝPremetricSpace .snd)
    (f x) (ℝPremetricSpace .snd)) →
  (∀ y → isContinuous (ℝPremetricSpace .snd)
    (λ x → g x y) (ℝPremetricSpace .snd)) →
  (∀ x → isContinuous (ℝPremetricSpace .snd)
    (g x) (ℝPremetricSpace .snd)) →
  (∀ p q → f (rat p) (rat q) ≡ g (rat p) (rat q)) →
  ∀ x y → f x y ≡ g x y
continuousExtensionality₂ =
  Ext.continuousExtensionality₂ ℝPremetricSpace

continuousExtensionality₃ :
  (f g : ℝ → ℝ → ℝ → ℝ) →
  (∀ y z → isContinuous (ℝPremetricSpace .snd)
    (λ x → f x y z) (ℝPremetricSpace .snd)) →
  (∀ x z → isContinuous (ℝPremetricSpace .snd)
    (λ y → f x y z) (ℝPremetricSpace .snd)) →
  (∀ x y → isContinuous (ℝPremetricSpace .snd)
    (f x y) (ℝPremetricSpace .snd)) →
  (∀ y z → isContinuous (ℝPremetricSpace .snd)
    (λ x → g x y z) (ℝPremetricSpace .snd)) →
  (∀ x z → isContinuous (ℝPremetricSpace .snd)
    (λ y → g x y z) (ℝPremetricSpace .snd)) →
  (∀ x y → isContinuous (ℝPremetricSpace .snd)
    (g x y) (ℝPremetricSpace .snd)) →
  (∀ p q r →
    f (rat p) (rat q) (rat r) ≡
    g (rat p) (rat q) (rat r)) →
  ∀ x y z → f x y z ≡ g x y z
continuousExtensionality₃ =
  Ext.continuousExtensionality₃ ℝPremetricSpace


-- The stronger graph-Cauchy universal property is retained without reducing
-- it to ordinary continuity.  This is the construction used by nonlinear
-- rational functions later in the development.

CauchyContinuousRestriction : Type₀
CauchyContinuousRestriction = C.CauchyContinuousRestriction

CauchyContinuousExtension : Type₀
CauchyContinuousExtension = C.CauchyContinuousExtension

extendCauchyContinuous :
  CauchyContinuousRestriction → CauchyContinuousExtension
extendCauchyContinuous = C.extendCauchyContinuous

restrictCauchyContinuous :
  CauchyContinuousExtension → CauchyContinuousRestriction
restrictCauchyContinuous = C.restrictCauchyContinuous

cauchyContinuousRestrictionExtensionIso :
  Iso CauchyContinuousRestriction CauchyContinuousExtension
cauchyContinuousRestrictionExtensionIso =
  C.cauchyContinuousRestrictionExtensionIso

cauchyContinuousRestrictionExtensionEquiv :
  CauchyContinuousRestriction ≃ CauchyContinuousExtension
cauchyContinuousRestrictionExtensionEquiv =
  C.cauchyContinuousRestrictionExtensionEquiv
