module Cubical.HITs.CauchyReals.Exponentiation.RealPower where

-- Public real-power facade.  Construction details stay in Infrastructure,
-- Construction, and Definition; clients get the operations and laws here.
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition public
  using
  ( _^ᵣ_
  ; ^ᵣ-mon-str
  ; ^-rat
  ; cont-^
  ; ^ᵣ0
  ; ^ᵣ1
  ; ^ᵣ[1/n]
  ; ^ᵣ+
  )
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Composition public
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Laws public
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Bounds public
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Calculus public
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.BaseContinuity public
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.BaseOrder public
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.LowerLipschitz public
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.NonzeroRealGroup public
