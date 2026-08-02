module Cubical.HITs.CauchyRealsP.Foundation.Rationals where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base hiding (isProp∼) public
open import Cubical.Data.Rationals.Order.AbsoluteValue public

open import Cubical.Algebra.OrderedCommRing public
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals public

open import Cubical.Relation.Premetric.Instances.Rationals public

open PositiveRationals public
open PositiveHalvesℚ public
open OrderedCommRingTheory ℚOrderedCommRing hiding (_#_) public

-- A qualified namespace keeps rational algebra readable in modules that also
-- introduce real operations with the same notation.
module ℚ where
  open import Cubical.Data.Rationals.Base hiding (isProp∼) public
  open import Cubical.Data.Rationals.Properties public
  open import Cubical.Data.Rationals.Order public
  open import Cubical.Data.Rationals.Order.AbsoluteValue public
  open import Cubical.Data.Rationals.Order.Algebra public
