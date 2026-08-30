module Cubical.Analysis.Real.UniversalProperty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Analysis.Real.Extensionality public

open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CauchyContinuous
  as CauchyContinuousDefinition

private
  module C =
    CauchyContinuousDefinition ℚPremetricSpace ℚPremetricSpace


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
