{-# OPTIONS --safe --cubical #-}

-- Worked applications, kept qualified to keep their scenario names local.
module Cubical.HITs.CauchyReals.Example.Financial.Examples where

module CommonScenarioData where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.CommonScenarioData public
module Diversification where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Diversification public
module Application where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Application public
module VarianceExample where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.VarianceExample public
module Rebalancing where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Rebalancing public
module TradeDecision where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.TradeDecision public
module StressConstrainedTrade where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.StressConstrainedTrade public
module RobustAllocation where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.RobustAllocation public
module ExecutionEquivalence where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.ExecutionEquivalence public
module DownstreamControl where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Dynamic.DownstreamControl public
module RectangularGap where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Dynamic.RectangularGap public
module OppositeClaims where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Netting.OppositeClaims public
module TwoCurrencyExample where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Settlement.TwoCurrencyExample public
module JointMoveExample where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.JointMoveExample public
module BrokerMargin where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.BrokerMargin public
module BrokerOperations where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.BrokerOperations public
module JointFXMargin where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.JointFXMargin public

-- Flagship system correctness statements, composing the worked components.
module BrokerGuarantees where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.BrokerGuarantees public
module TradingGuarantees where
  open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.TradingGuarantees public
