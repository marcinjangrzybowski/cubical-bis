{-# OPTIONS --safe --cubical #-}

-- A single end-to-end contract for the data returned by Implementation.process.
-- Cubical paths compare the resulting state AND its state-indexed report.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties.Refinement where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Experiments.Relation.Base using (Fields; Row'; ⟦_⟧; _,,_; [])
open import Cubical.Experiments.Relation.Operations using (tabulateᵣ; tabulate-cong)
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Sources as Source
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties.Correctness as Correctness
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V04Rational as Rational
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V03Stress as Stress

module Refinement {clients trades instruments lots assets receipts stresses : ℕ}
  (sources : Source.Schema.DataSources clients trades instruments lots assets receipts stresses) where
  open Source.Schema clients trades instruments lots assets receipts stresses
  module Engine = Correctness.Pipeline sources
  open Engine

  report-refines-model : ∀ s report next deliveries →
    PathP (λ i → Abstract.Report (receive-refines-model s next deliveries i))
      (advanceReport s report next deliveries) (modelNextReport s report next deliveries)
  report-refines-model s report next deliveries i .Rational.amounts client =
    nextAmounts-refine s report next deliveries client i
  report-refines-model s report next deliveries i .Rational.amounts-nonnegative client =
    isProp→PathP (λ j → ℚ.isProp≤ 0 (nextAmounts-refine s report next deliveries client j))
      (Rational.amounts-nonnegative (advanceReport s report next deliveries) client)
      (Rational.amounts-nonnegative (modelNextReport s report next deliveries) client) i
  report-refines-model s report next deliveries i .Rational.dominates client =
    isProp→PathP (λ j → isProp≤ᵣ
      (Stress.quoteCall (Abstract.view (receive-refines-model s next deliveries j)) client)
      (rat (nextAmounts-refine s report next deliveries client j)))
      (Rational.dominates (advanceReport s report next deliveries) client)
      (Rational.dominates (modelNextReport s report next deliveries) client) i

  process-refines-model : ∀ s report next mta mta₊ deliveries →
    Path (Σ Abstract.State Abstract.Report)
      (decode (Code.next-state (Code.process s (Rational.amounts report) next mta deliveries)) ,
        advanceReport s report next deliveries)
      (Abstract.Old.next-state (Abstract.process (decode s) report (certifiedUpdate s next) mta mta₊
          (Cash.decodeBatch deliveries)) ,
        Abstract.Old.next-report (Abstract.process (decode s) report (certifiedUpdate s next) mta mta₊
          (Cash.decodeBatch deliveries)))
  process-refines-model s report next mta mta₊ deliveries i =
    receive-refines-model s next deliveries i , report-refines-model s report next deliveries i

  -- The output table retains business references while its numeric columns
  -- agree with the abstract quote and refreshed report for each client key.
  modelCallRows : ∀ s → Report s → Valuation → Rational.Payments clients → ⟦ MarginCalls ⟧
  modelCallRows s report next mta = tabulateᵣ (λ client →
    client ,, clientReference sources client ,, snapshotId next ,,
    Rational.amounts (Abstract.refreshReport (decode s) report (certifiedUpdate s next)) client ,,
    mta client ,, Abstract.quoteCall (decode s) report (certifiedUpdate s next) mta client ,, [])

  callRows-refine-model : ∀ s report next mta → Code.callRows s (Rational.amounts report) next mta ≡ modelCallRows s report next mta
  callRows-refine-model s report next mta = tabulate-cong _ _ (λ client →
    cong {B = λ _ → Row' (Fields.fields MarginCalls)} (λ requested →
      client ,, clientReference sources client ,, snapshotId next ,,
      Code.upperAfterRevaluation s (Rational.amounts report) next client ,, mta client ,, requested ,, [])
      (funExt⁻ (quote-refines-model s report next mta) client))

  record Compliance (s : State) (report : Report s) (next : Valuation)
    (mta : Rational.Payments clients) (mta₊ : Rational.Nonnegative mta)
    (deliveries : Cash.Deliveries) : Type₁ where
    private
      output = Code.process s (Rational.amounts report) next mta deliveries
      modelOutput = Abstract.process (decode s) report (certifiedUpdate s next) mta mta₊ (Cash.decodeBatch deliveries)
    field
      state-and-report-match : Path (Σ Abstract.State Abstract.Report)
        (decode (Code.next-state output) , advanceReport s report next deliveries)
        (Abstract.Old.next-state modelOutput , Abstract.Old.next-report modelOutput)
      remaining-match : Code.next-amounts output ≡ Rational.amounts (Abstract.Old.next-report modelOutput)
      calls-match : Code.calls output ≡ modelCallRows s report next mta
      execution-certified : CertifiedOutput s report next mta deliveries
      financial-guarantee : Adequate s report next mta deliveries → Guarantee (Code.next-state output) mta
  open Compliance public

  pipeline-correct : ∀ s report next mta mta₊ deliveries → Compliance s report next mta mta₊ deliveries
  pipeline-correct s report next mta mta₊ deliveries .state-and-report-match =
    process-refines-model s report next mta mta₊ deliveries
  pipeline-correct s report next mta mta₊ deliveries .remaining-match =
    funExt (nextAmounts-refine s report next deliveries)
  pipeline-correct s report next mta mta₊ deliveries .execution-certified = certify s report next mta mta₊ deliveries
  pipeline-correct s report next mta mta₊ deliveries .calls-match = callRows-refine-model s report next mta
  pipeline-correct s report next mta mta₊ deliveries .financial-guarantee =
    reference-guarantee s report next mta mta₊ deliveries
