{-# OPTIONS --safe --cubical #-}

-- Compatibility umbrella: preserves existing imports and nested example names.
-- New clients may import Financial.Theory and qualified Financial.Examples.
module Cubical.HITs.CauchyReals.Example.Financial where

module Theory where
  open import Cubical.HITs.CauchyReals.Example.Financial.Theory public
module Examples where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples public

open import Cubical.HITs.CauchyReals.Example.Financial.Finite public
open import Cubical.HITs.CauchyReals.Example.Financial.Probability public
open import Cubical.HITs.CauchyReals.Example.Financial.Shortfall public
open import Cubical.HITs.CauchyReals.Example.Financial.WorstCase public
open import Cubical.HITs.CauchyReals.Example.Financial.ExpectedShortfall public
open import Cubical.HITs.CauchyReals.Example.Financial.RiskLaws public
open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio public
open import Cubical.HITs.CauchyReals.Example.Financial.EconomicEquivalence public
open import Cubical.HITs.CauchyReals.Example.Financial.RiskControl public
open import Cubical.HITs.CauchyReals.Example.Financial.Policy public
open import Cubical.HITs.CauchyReals.Example.Financial.Variance public
open import Cubical.HITs.CauchyReals.Example.Financial.TransactionCosts public
open import Cubical.HITs.CauchyReals.Example.Financial.Ambiguity public
open import Cubical.HITs.CauchyReals.Example.Financial.DynamicRisk public
open import Cubical.HITs.CauchyReals.Example.Financial.DynamicAmbiguity public
open import Cubical.HITs.CauchyReals.Example.Financial.FXSwap public
open import Cubical.HITs.CauchyReals.Example.Financial.FXBounds public
open import Cubical.HITs.CauchyReals.Example.Financial.Margin public
open import Cubical.HITs.CauchyReals.Example.Financial.MarginControl public
open import Cubical.HITs.CauchyReals.Example.Financial.ClientNetting public
open import Cubical.HITs.CauchyReals.Example.Financial.CounterpartyRisk public
open import Cubical.HITs.CauchyReals.Example.Financial.Settlement public

module Diversification where
  open import Cubical.HITs.CauchyReals.Example.Financial.Diversification public
module Application where
  open import Cubical.HITs.CauchyReals.Example.Financial.Application public
module VarianceExample where
  open import Cubical.HITs.CauchyReals.Example.Financial.VarianceExample public
module Rebalancing where
  open import Cubical.HITs.CauchyReals.Example.Financial.Rebalancing public
module TradeDecision where
  open import Cubical.HITs.CauchyReals.Example.Financial.TradeDecision public
module StressConstrainedTrade where
  open import Cubical.HITs.CauchyReals.Example.Financial.StressConstrainedTrade public
module RobustAllocation where
  open import Cubical.HITs.CauchyReals.Example.Financial.RobustAllocation public
module ExecutionEquivalence where
  open import Cubical.HITs.CauchyReals.Example.Financial.ExecutionEquivalence public
module BrokerMargin where
  open import Cubical.HITs.CauchyReals.Example.Financial.BrokerMargin public
module BrokerOperations where
  open import Cubical.HITs.CauchyReals.Example.Financial.BrokerOperations public
module JointFXMargin where
  open import Cubical.HITs.CauchyReals.Example.Financial.JointFXMargin public

open ExecutionEquivalence public using (module ExecutionModel)
