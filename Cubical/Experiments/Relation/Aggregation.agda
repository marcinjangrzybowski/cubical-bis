{-# OPTIONS --safe --cubical #-}

module Cubical.Experiments.Relation.Aggregation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin)
import Cubical.Data.FinData.Base as F
open import Cubical.Data.FinData.Properties using (discreteFin)
open import Cubical.Data.List.Base using ([]; _∷_; _++_)
open import Cubical.Data.Bool.Base using (Bool; true; false; if_then_else_; Dec→Bool)
open import Cubical.Relation.Nullary using (yes; no)
open import Agda.Builtin.String using (String)
open import Cubical.Experiments.Relation.Base using
  (Fields'; Row'; Relation'; []; _∶_,_; _,,_;
   NonMember; insertField; insert; insertᵣ)
open import Cubical.Experiments.Relation.Operations

-- Definitions and the first laws need no algebraic assumptions. In
-- particular, the row order and repeated-row contributions are preserved.
module Sum (A : Type₀) (zeroA : A) (_+A_ : A → A → A) where
  sumBy : ∀ {schema} → (Row' schema → A) → Relation' schema → A
  sumBy weight [] = zeroA
  sumBy weight (row ∷ rows) = weight row +A sumBy weight rows

  finiteSum : ∀ {n} → (Fin n → A) → A
  finiteSum {zero} values = zeroA
  finiteSum {suc n} values = values F.zero +A finiteSum (λ i → values (F.suc i))

  selected : ∀ {schema} → (Row' schema → Bool) → (Row' schema → A) → Row' schema → A
  selected predicate weight row = if predicate row then weight row else zeroA

  sum-cong : ∀ {schema} (left right : Row' schema → A) rows →
    (∀ row → left row ≡ right row) → sumBy left rows ≡ sumBy right rows
  sum-cong left right rows same = cong (λ weight → sumBy weight rows) (funExt same)

  sum-tabulate : ∀ {n schema} (weight : Row' schema → A) (rows : Fin n → Row' schema) →
    sumBy weight (tabulateᵣ rows) ≡ finiteSum (λ i → weight (rows i))
  sum-tabulate {zero} weight rows = refl
  sum-tabulate {suc n} weight rows =
    cong (weight (rows F.zero) +A_) (sum-tabulate weight (λ i → rows (F.suc i)))

  sum-project : ∀ {source target} (project : Row' source → Row' target)
    (weight : Row' target → A) rows →
    sumBy weight (projectᵣ project rows) ≡ sumBy (λ row → weight (project row)) rows
  sum-project project weight [] = refl
  sum-project project weight (row ∷ rows) =
    cong (weight (project row) +A_) (sum-project project weight rows)

  -- These laws follow the column-building stages of a relation pipeline.
  -- No commutativity or identity law for the aggregate is needed.
  sum-derive : (name : String) {Ty : Type₀} {source : Fields'} →
    ⦃ fresh : NonMember name source ⦄ → (compute : Row' source → Ty) →
    (weight : Row' (insertField name {Ty = Ty} {source = source}) → A) →
    (rows : Relation' source) →
    sumBy weight (deriveᵣ name compute rows)
      ≡ sumBy (λ row → weight (insert name (compute row) row)) rows
  sum-derive name compute weight rows =
    sum-project (λ row → insert name (compute row) row) weight rows

  sum-insert : (name : String) {Ty : Type₀} {source : Fields'} →
    ⦃ fresh : NonMember name source ⦄ → (value : Ty) →
    (weight : Row' (insertField name {Ty = Ty} {source = source}) → A) →
    (rows : Relation' source) →
    sumBy weight (insertᵣ name value rows)
      ≡ sumBy (λ row → weight (insert name value row)) rows
  sum-insert name value weight rows = sum-project (insert name value) weight rows

  sum-select : (left-zero : ∀ x → zeroA +A x ≡ x) →
    ∀ {schema} (predicate : Row' schema → Bool) weight rows →
    sumBy weight (selectᵣ predicate rows) ≡ sumBy (selected predicate weight) rows
  sum-select left-zero predicate weight [] = refl
  sum-select left-zero predicate weight (row ∷ rows) with predicate row
  ... | true = cong (weight row +A_) (sum-select left-zero predicate weight rows)
  ... | false = sum-select left-zero predicate weight rows
    ∙ sym (left-zero (sumBy (selected predicate weight) rows))

  sum-append : (left-zero : ∀ x → zeroA +A x ≡ x) →
    (assoc : ∀ x y z → (x +A y) +A z ≡ x +A (y +A z)) →
    ∀ {schema} (weight : Row' schema → A) left right →
    sumBy weight (left ++ right) ≡ sumBy weight left +A sumBy weight right
  sum-append left-zero assoc weight [] right = sym (left-zero (sumBy weight right))
  sum-append left-zero assoc weight (row ∷ rows) right =
    cong (weight row +A_) (sum-append left-zero assoc weight rows right)
    ∙ sym (assoc (weight row) (sumBy weight rows) (sumBy weight right))

  -- The decision matches fixed finite identifiers, not amounts. Each row
  -- contributes to its own key and to no different key.
  atKey : ∀ {n schema} → (Row' schema → Fin n) → (Row' schema → A) →
    Fin n → Row' schema → A
  atKey key weight query row with discreteFin (key row) query
  ... | yes same = weight row
  ... | no different = zeroA

  atKey-selected : ∀ {n schema} (key : Row' schema → Fin n) weight query row →
    atKey key weight query row
      ≡ selected (λ item → Dec→Bool (discreteFin (key item) query)) weight row
  atKey-selected key weight query row with discreteFin (key row) query
  ... | yes same = refl
  ... | no different = refl

  groupSum : ∀ {n schema} → (Row' schema → Fin n) → (Row' schema → A) →
    Relation' schema → Fin n → A
  groupSum key weight rows query = sumBy (atKey key weight query) rows

  group-tabulate : ∀ {n count schema} (key : Row' schema → Fin n) weight
    (rows : Fin count → Row' schema) query →
    groupSum key weight (tabulateᵣ rows) query
      ≡ finiteSum (λ i → atKey key weight query (rows i))
  group-tabulate key weight rows query = sum-tabulate (atKey key weight query) rows

  GroupFields : ℕ → Fields'
  GroupFields n = "key" ∶ Fin n , "total" ∶ A , []

  -- A dense result contains each finite key, including keys with no input
  -- rows. Their total is the empty sum when left-zero is available.
  groupRows : ∀ {n schema} → (Row' schema → Fin n) → (Row' schema → A) →
    Relation' schema → Relation' (GroupFields n)
  groupRows key weight rows = tabulateᵣ (λ query → query ,, groupSum key weight rows query ,, [])
