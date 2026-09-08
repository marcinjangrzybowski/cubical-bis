{-# OPTIONS --safe --cubical #-}

-- Compatibility import. Implementation: Dynamic/Ambiguity.agda
module Cubical.HITs.CauchyReals.Example.Financial.DynamicAmbiguity where

open import Cubical.HITs.CauchyReals.Example.Financial.Dynamic.Ambiguity public

module RectangularGap where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Dynamic.RectangularGap public

open import Cubical.HITs.CauchyReals.Example.Financial.DynamicRisk public using (module DownstreamControl)
