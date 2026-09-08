{-# OPTIONS --safe --cubical #-}

-- The properties refer to the actual table returned by the read-only
-- calculation. Its rows agree with the model, including requested amounts.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties.Calculation where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Data.List.Base using ([]; _∷_)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_×_)
import Cubical.Data.FinData.Base as F
open import Cubical.Experiments.Relation.Base using
  (Fields; Fields'; Row'; Relation'; _∶_,_; []; _,,_; insert; ⟦_⟧)
open import Cubical.Experiments.Relation.Operations
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Sources as Source
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Calculation as Implementation
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Margin as Policy
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties.Correctness as Correctness
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V05Tolerance as Tolerance
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V04Rational as Rational
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V03Stress as Stress

EveryRow : ∀ {schema} → (Row' schema → Type₀) → Relation' schema → Type₀
EveryRow predicate [] = Unit
EveryRow predicate (row ∷ rows) = predicate row × EveryRow predicate rows

private
  every-tabulate : ∀ {n schema} (predicate : Row' schema → Type₀)
    (rows : Fin n → Row' schema) → (∀ i → predicate (rows i)) →
    EveryRow predicate (tabulateᵣ rows)
  every-tabulate {zero} predicate rows proofs = tt
  every-tabulate {suc n} predicate rows proofs = proofs F.zero ,
    every-tabulate predicate (λ i → rows (F.suc i)) (λ i → proofs (F.suc i))

  every-tabulate-at : ∀ {n schema} (predicate : Row' schema → Type₀)
    (rows : Fin n → Row' schema) → EveryRow predicate (tabulateᵣ rows) →
    ∀ i → predicate (rows i)
  every-tabulate-at {suc n} predicate rows proofs F.zero = fst proofs
  every-tabulate-at {suc n} predicate rows proofs (F.suc i) =
    every-tabulate-at predicate (λ j → rows (F.suc j)) (snd proofs) i

module Calculation {clients trades instruments lots assets receipts stresses : ℕ}
  (sources : Source.Schema.DataSources clients trades instruments lots assets receipts stresses) where
  open Source.Schema clients trades instruments lots assets receipts stresses
  module Code = Implementation.MarginCalculation sources
  module Engine = Correctness.Pipeline sources
  module Maximum = Implementation.Maximum

  private
    ClientKeys ScenarioKeys UpperKeys RequestedKeys : Fields'
    ClientKeys = "clientId" ∶ ClientId , []
    ScenarioKeys = "scenarioId" ∶ ScenarioId , []
    UpperKeys = "incrementalUpper" ∶ ℚ , ClientKeys
    RequestedKeys = "requestedCash" ∶ ℚ , UpperKeys

    clientRow : ClientId → Row' ClientKeys
    clientRow client = client ,, []

    scenarioRow : ScenarioId → Row' ScenarioKeys
    scenarioRow scenario = scenario ,, []

    gap : Valuation → Code.Receipts.Ledger → ClientId → Row' ScenarioKeys → ℚ
    gap valuation seen client row = ℚ.max
      (Engine.Values.claimTotals valuation (get "scenarioId" row) client ℚ.-
        (Engine.Values.collateralTotals valuation (get "scenarioId" row) client
          ℚ.+ Engine.Cash.balances seen client)) 0

    required : Valuation → Code.Receipts.Ledger → ClientId → ℚ
    required valuation seen client = Maximum.sumBy (get "requiredCash")
      (deriveᵣ "requiredCash" (gap valuation seen client) (tabulateᵣ scenarioRow))

    required-exact : ∀ valuation seen client → required valuation seen client
      ≡ Engine.Code.initialAmounts (Engine.state valuation seen) client
    required-exact valuation seen client =
      Maximum.sum-derive "requiredCash" (gap valuation seen client)
        (get "requiredCash") (tabulateᵣ scenarioRow)
      ∙ Maximum.sum-tabulate
        (λ row → get "requiredCash" (insert "requiredCash" (gap valuation seen client row) row)) scenarioRow

    tableRow : Valuation → (ClientId → ℚ) → ClientId → ℚ → ℚ → Row' (Fields.fields MarginCalls)
    tableRow valuation mta client upper requested = client ,, clientReference sources client ,,
      snapshotId valuation ,, upper ,, mta client ,, requested ,, []

    calculate-tabulated : ∀ valuation seen mta → Code.calculate valuation seen mta ≡
      tabulateᵣ (λ client → tableRow valuation mta client (required valuation seen client)
        (Policy.transferAmount (required valuation seen client) (mta client)))
    calculate-tabulated valuation seen mta =
      cong (projectᵣ finish) (project-compose addUpper addRequest (tabulateᵣ clientRow))
      ∙ project-compose (λ row → addRequest (addUpper row)) finish (tabulateᵣ clientRow)
      ∙ project-tabulate (λ row → finish (addRequest (addUpper row))) clientRow
      where
      addUpper : Row' ClientKeys → Row' UpperKeys
      addUpper row = insert "incrementalUpper" (required valuation seen (get "clientId" row)) row
      addRequest : Row' UpperKeys → Row' RequestedKeys
      addRequest row = insert "requestedCash"
        (Policy.transferAmount (get "incrementalUpper" row) (mta (get "clientId" row))) row
      finish : Row' RequestedKeys → Row' (Fields.fields MarginCalls)
      finish row = tableRow valuation mta (get "clientId" row)
        (get "incrementalUpper" row) (get "requestedCash" row)

  modelRow : Valuation → Code.Receipts.Ledger → (ClientId → ℚ) → ClientId → Row' (Fields.fields MarginCalls)
  modelRow valuation seen mta client = tableRow valuation mta client
    (Rational.amounts (Engine.initialReport s) client)
    (Engine.Abstract.Old.quoteCall (Engine.decode s) (Engine.initialReport s) mta client)
    where s = Engine.state valuation seen

  modelRows : Valuation → Code.Receipts.Ledger → (ClientId → ℚ) → ⟦ MarginCalls ⟧
  modelRows valuation seen mta = tabulateᵣ (modelRow valuation seen mta)

  -- This equality covers every column and the actual output order and
  -- multiplicity: one row per client, including clients with empty groups.
  calculate-refines-model : ∀ valuation seen mta →
    Code.calculate valuation seen mta ≡ modelRows valuation seen mta
  calculate-refines-model valuation seen mta = calculate-tabulated valuation seen mta
    ∙ tabulate-cong
      (λ client → tableRow valuation mta client (required valuation seen client)
        (Policy.transferAmount (required valuation seen client) (mta client)))
      (modelRow valuation seen mta) (λ client → cong₂ (tableRow valuation mta client)
      (required-exact valuation seen client)
      (cong (λ upper → Policy.transferAmount upper (mta client)) (required-exact valuation seen client)
        ∙ Engine.transfer-refines-model (Engine.Code.initialAmounts (Engine.state valuation seen) client) (mta client)))

  referenceBook : Valuation → Code.Receipts.Ledger → Stress.State clients stresses
  referenceBook valuation seen = Engine.Abstract.view
    (Engine.referenceState (Engine.state valuation seen))

  record RowCertified (valuation : Valuation) (seen : Code.Receipts.Ledger)
    (mta : ClientId → ℚ) (row : Row' (Fields.fields MarginCalls)) : Type₀ where
    private
      client = get "clientId" row
      s = Engine.state valuation seen
    field
      client-reference-correct : get "externalClientId" row ≡ clientReference sources client
      snapshot-correct : get "snapshotId" row ≡ snapshotId valuation
      upper-exact : Stress.quoteCall (referenceBook valuation seen) client
        ≡ rat (get "incrementalUpper" row)
      upper-nonnegative : 0 ℚ.≤ get "incrementalUpper" row
      tolerance-correct : get "minimumTransfer" row ≡ mta client
      request-exact : get "requestedCash" row
        ≡ Engine.Abstract.Old.quoteCall (Engine.decode s) (Engine.initialReport s) mta client
      request-nonnegative : 0 ℚ.≤ get "requestedCash" row
  open RowCertified public

  private
    model-row-certified : ∀ valuation seen mta client →
      RowCertified valuation seen mta (modelRow valuation seen mta client)
    model-row-certified valuation seen mta client .client-reference-correct = refl
    model-row-certified valuation seen mta client .snapshot-correct = refl
    model-row-certified valuation seen mta client .upper-exact =
      sym (cong (λ t → Stress.quoteCall (Engine.Abstract.view t) client)
        (Engine.decode-refines-reference (Engine.state valuation seen)))
      ∙ Engine.initial-quote-exact (Engine.state valuation seen) client
    model-row-certified valuation seen mta client .upper-nonnegative =
      Rational.amounts-nonnegative (Engine.initialReport (Engine.state valuation seen)) client
    model-row-certified valuation seen mta client .tolerance-correct = refl
    model-row-certified valuation seen mta client .request-exact = refl
    model-row-certified valuation seen mta client .request-nonnegative =
      Tolerance.quote-nonnegative
        (Engine.Abstract.view (Engine.decode (Engine.state valuation seen)))
        (Engine.initialReport (Engine.state valuation seen)) mta client

  -- Every row of the actual returned table carries an exact least upper
  -- requirement and the model's request, with its client and snapshot data.
  -- Nonnegative MTAs are needed for the risk bound below, not for this equality.
  calculate-certified : ∀ valuation seen mta →
    EveryRow (RowCertified valuation seen mta) (Code.calculate valuation seen mta)
  calculate-certified valuation seen mta =
    subst (EveryRow (RowCertified valuation seen mta))
      (sym (calculate-refines-model valuation seen mta))
      (every-tabulate (RowCertified valuation seen mta) (modelRow valuation seen mta)
        (model-row-certified valuation seen mta))

  -- Each receipt is routed using the client ID in the returned row. There
  -- is no comparison of pooled payments with a pooled requested amount.
  MeetsRequests : (ClientId → ℚ) → ⟦ MarginCalls ⟧ → Type₀
  MeetsRequests paid = EveryRow (λ row → get "requestedCash" row ℚ.≤ paid (get "clientId" row))

  -- The calculation itself receives no cash. This consequence is conditional
  -- on the supplied nonnegative amounts actually being received and remaining
  -- eligible for their client. It concerns the independent source-sum book.
  -- paid is ADDITIONAL cash beyond seen, not a closing balance. For delivery
  -- messages use the receipt pipeline's deltaBalances and accounting proofs;
  -- this amount-based consequence does not itself deduplicate receipt IDs.
  fulfilling-calculation : ∀ valuation seen mta → Rational.Nonnegative mta →
    ∀ paid paid₊ → MeetsRequests paid (Code.calculate valuation seen mta) →
    Tolerance.Guarantee (Rational.receive (referenceBook valuation seen) paid paid₊) mta
  fulfilling-calculation valuation seen mta mta₊ paid paid₊ enough =
    subst (λ b → Tolerance.Guarantee b mta)
      (cong (λ t → Rational.receive (Engine.Abstract.view t) paid paid₊)
        (Engine.decode-refines-reference s))
      (Tolerance.guarantee (Rational.receive book paid paid₊) mta
        (Tolerance.receive-correct book (Engine.initialReport s) mta mta₊ paid paid₊ adequate))
    where
    s = Engine.state valuation seen
    book = Engine.Abstract.view (Engine.decode s)
    adequate : Tolerance.Adequate book (Engine.initialReport s) mta paid
    adequate = every-tabulate-at
      (λ row → get "requestedCash" row ℚ.≤ paid (get "clientId" row))
      (modelRow valuation seen mta)
      (subst (MeetsRequests paid) (calculate-refines-model valuation seen mta) enough)
