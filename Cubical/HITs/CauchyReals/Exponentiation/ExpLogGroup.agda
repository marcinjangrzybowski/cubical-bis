module Cubical.HITs.CauchyReals.Exponentiation.ExpLogGroup where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.ExponentiationMore using (^ᵣ+)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPowerBase
  using (+Groupℝ; ·₊Groupℝ)
open import Cubical.HITs.CauchyReals.Exponentiation.ExpLog

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

realExpGroupHom : GroupHom +Groupℝ ·₊Groupℝ
realExpGroupHom .fst = realExp
realExpGroupHom .snd = makeIsGroupHom (^ᵣ+ eBase)

realExpGroupIso : GroupIso +Groupℝ ·₊Groupℝ
realExpGroupIso = expLogIso , snd realExpGroupHom
