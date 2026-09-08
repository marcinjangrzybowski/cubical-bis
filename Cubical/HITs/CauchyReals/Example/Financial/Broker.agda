{-# OPTIONS --safe --cubical #-}

-- Generic staged broker machinery. No worked scenarios or market data.
module Cubical.HITs.CauchyReals.Example.Financial.Broker where

module Stage01Cash where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage01Cash public

module Stage02Scenarios where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage02Scenarios public

module Stage03NettingSets where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage03NettingSets public

module Stage04Collateral where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage04Collateral public

module Stage05Journal where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage05Journal public

module Stage06Revaluation where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage06Revaluation public

module Stage07Calls where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage07Calls public

module Stage08Controller where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage08Controller public
