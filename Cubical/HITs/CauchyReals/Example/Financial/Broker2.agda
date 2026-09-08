{-# OPTIONS --safe --cubical #-}

-- Successive verified versions of one broker margin engine.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2 where

module V01Account where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V01Account public

module V02Clients where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V02Clients public

module V03Stress where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V03Stress public

module V04Rational where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V04Rational public

module V05Tolerance where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V05Tolerance public

module V06Receipts where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V06Receipts public

module V07Revaluation where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V07Revaluation public

module Pipeline where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline public
