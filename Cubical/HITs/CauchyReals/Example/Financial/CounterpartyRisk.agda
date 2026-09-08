{-# OPTIONS --safe --cubical #-}

-- Compatibility import. Implementation: Margin/CounterpartyRisk.agda
module Cubical.HITs.CauchyReals.Example.Financial.CounterpartyRisk where

open import Cubical.HITs.CauchyReals.Example.Financial.Margin.CounterpartyRisk public

open import Cubical.HITs.CauchyReals.Example.Financial.ClientNetting public using (module OppositeClaims)
