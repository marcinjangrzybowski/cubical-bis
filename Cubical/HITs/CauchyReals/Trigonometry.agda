module Cubical.HITs.CauchyReals.Trigonometry where

-- Public facade for trigonometric functions, pi, and identities.
open import Cubical.HITs.CauchyReals.Trigonometry.Base public
open import Cubical.HITs.CauchyReals.Trigonometry.Pi public
  hiding (module ℚO)
open import Cubical.HITs.CauchyReals.Trigonometry.Identities public
