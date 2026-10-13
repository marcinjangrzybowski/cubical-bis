module Cubical.Analysis.Complex.FundamentalTheorem.Completion.FiniteSearch where

-- An inhabited decidable predicate on naturals has a unique least witness.
-- Finding it searches only below a supplied witness. Uniqueness permits
-- elimination of a truncated existence proof, without a choice principle.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as N
import Cubical.Data.Nat.Order.Recursive as Recursive
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary using (Dec)
import Cubical.HITs.PropositionalTruncation as PT

LeastWitness : (ℕ → Type₀) → Type₀
LeastWitness P = Σ[ k ∈ ℕ ] P k × (∀ j → P j → k N.≤ j)

leastWitness-prop : ∀ P → (∀ k → isProp (P k)) → isProp (LeastWitness P)
leastWitness-prop P prop (k , pk , least-k) (l , pl , least-l) =
  Σ≡Prop (λ j → isProp× (prop j) (isPropΠ2 λ _ _ → N.isProp≤))
    (N.≤-antisym (least-k l pl) (least-l k pk))

private
  -- The library search uses recursive order; retain this module's usual
  -- additive-witness order in its public least-witness certificate.
  ≤→recursive : ∀ {m n} → m N.≤ n → m Recursive.≤ n
  ≤→recursive {zero} bound = tt
  ≤→recursive {suc m} {zero} bound = Empty.rec (N.¬-<-zero bound)
  ≤→recursive {suc m} {suc n} bound = ≤→recursive (N.pred-≤-pred bound)

searchBelowWitness : ∀ P → (∀ k → Dec (P k)) → (k : ℕ) → P k → LeastWitness P
searchBelowWitness P decide k witness with Recursive.Minimal.→Least decide (k , witness)
... | j , present , no-earlier = j , present , λ l pl →
  N.<-asym' (λ l<j → no-earlier l (≤→recursive l<j) pl)

firstWitness : ∀ P → (∀ k → isProp (P k)) → (∀ k → Dec (P k)) →
  PT.∥ Σ[ k ∈ ℕ ] P k ∥₁ → Σ[ k ∈ ℕ ] P k
firstWitness P prop decide inhabited = fst least , fst (snd least)
  where
  least : LeastWitness P
  least = PT.rec (leastWitness-prop P prop)
    (λ { (k , witness) → searchBelowWitness P decide k witness }) inhabited
