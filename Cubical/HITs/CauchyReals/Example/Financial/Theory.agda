{-# OPTIONS --safe --cubical #-}

-- Reusable theory only. No dependency on Financial.Examples or legacy shims.
module Cubical.HITs.CauchyReals.Example.Financial.Theory where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
open import Cubical.HITs.CauchyReals.Example.Financial.Core.Vectors public
open import Cubical.HITs.CauchyReals.Example.Financial.Core.Bounds public
open import Cubical.HITs.CauchyReals.Example.Financial.Core.Probability public
open import Cubical.HITs.CauchyReals.Example.Financial.Core.EconomicEquivalence public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.FiniteShortfall public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.ExpectedShortfall public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.RiskLaws public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Variance public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Ambiguity public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.RiskControl public
open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.Base public
open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.TransactionCosts public
open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.Policy public
open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.ExecutionEquivalence public
open import Cubical.HITs.CauchyReals.Example.Financial.Dynamic.Base public
open import Cubical.HITs.CauchyReals.Example.Financial.Dynamic.Ambiguity public
open import Cubical.HITs.CauchyReals.Example.Financial.Instruments.FXSwap public
open import Cubical.HITs.CauchyReals.Example.Financial.Instruments.FXBounds public
open import Cubical.HITs.CauchyReals.Example.Financial.Margin.Scenario public
open import Cubical.HITs.CauchyReals.Example.Financial.Margin.Base public
open import Cubical.HITs.CauchyReals.Example.Financial.Margin.MarginControl public
open import Cubical.HITs.CauchyReals.Example.Financial.Margin.ClientNetting public
open import Cubical.HITs.CauchyReals.Example.Financial.Margin.CounterpartyRisk public
open import Cubical.HITs.CauchyReals.Example.Financial.Settlement.Base public

-- Workflow statuses and receipt fields keep their own public namespaces.
module MarginWorkflow where
  open import Cubical.HITs.CauchyReals.Example.Financial.Margin.Workflow public
module PaymentHistory where
  open import Cubical.HITs.CauchyReals.Example.Financial.Margin.PaymentHistory public

-- Increasingly rich generic broker controls, with their own stage namespaces.
module Broker where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker public

-- Presentation: one engine with proved version-to-version relationships.
module Broker2 where
  open import Cubical.HITs.CauchyReals.Example.Financial.Broker2 public
