{-# OPTIONS --safe --cubical #-}

-- Compatibility import. Implementation: Margin/ClientNetting.agda
module Cubical.HITs.CauchyReals.Example.Financial.ClientNetting where

open import Cubical.HITs.CauchyReals.Example.Financial.Margin.ClientNetting public

module OppositeClaims where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Netting.OppositeClaims public
