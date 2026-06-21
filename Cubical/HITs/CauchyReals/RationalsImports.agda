module Cubical.HITs.CauchyReals.RationalsImports where


open import Cubical.Tactics.CommRingSolver.Specialised.Rationals public

open import Cubical.Tactics.CommRingSolver.OrderedReflection public


open import Cubical.Tactics.CommRingSolver public

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals public
open import Cubical.Tactics.CommRingSolver.OrderedReflection  public


open import Cubical.Algebra.CommRing.Instances.Rationals public
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.OrderedCommRing public
open import Cubical.Algebra.OrderedCommRing.Properties public
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals public

import Cubical.Algebra.CommRing as CR
open import Cubical.Algebra.CommRing.Properties public

open import Cubical.Data.Sigma
open PositiveRationals public
open PositiveHalvesℚ public
open OrderedCommRingTheory ℚOrderedCommRing hiding (_#_) public

open import Cubical.Data.Rationals.Base public

module ℚ where
 
 open import Cubical.Data.Rationals.Base public
 open import Cubical.Data.Rationals.Properties public
 open import Cubical.Data.Rationals.Order public
 open import Cubical.Data.Rationals.Order.AbsoluteValue public
 open import Cubical.Data.Rationals.Order.Floor public
 open import Cubical.Data.Rationals.Order.Algebra public
 open import Cubical.Data.Rationals.Inverse public


module Rℚ where
 ℚRing = (CR.CommRing→Ring ℚCommRing)
 open CR.CommRingStr (snd (ℚCommRing)) public
 open RingTheory ℚRing public
 open CR.CommRingTheory ℚCommRing public

 
