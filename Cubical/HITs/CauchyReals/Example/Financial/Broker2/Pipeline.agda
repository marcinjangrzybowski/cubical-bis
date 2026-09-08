{-# OPTIONS --safe --cubical #-}

-- The two imports expose computation and certification separately.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline where

module Implementation where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation public

module Properties where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties public
