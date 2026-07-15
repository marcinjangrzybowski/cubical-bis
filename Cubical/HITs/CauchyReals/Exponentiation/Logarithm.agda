module Cubical.HITs.CauchyReals.Exponentiation.Logarithm where

-- Public logarithm facade.  The construction is shared with real powers, but
-- only logarithm-facing names are re-exported here.
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition public
  using
  ( ln
  ; ln-c
  ; ln-1≡0
  ; ln-cont
  ; ln-inv
  ; 1<a→0<ln[a]
  )
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Order public
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Laws public
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Derivative public
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.DerivativeBounds public
