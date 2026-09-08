{-# OPTIONS --safe --cubical #-}

module Cubical.Experiments.Relation.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin)
import Cubical.Data.FinData.Base as F
open import Cubical.Data.List.Base using ([]; _∷_; map)
open import Cubical.Data.Bool.Base using (Bool; true; false)
open import Cubical.Experiments.Relation.Base using (Fields'; Row'; Relation')

-- Relations retain list order and multiplicity. These operations do not
-- silently deduplicate rows or assume uniqueness of field values.
tabulateᵣ : ∀ {n} {schema : Fields'} → (Fin n → Row' schema) → Relation' schema
tabulateᵣ {zero} rows = []
tabulateᵣ {suc n} rows = rows F.zero ∷ tabulateᵣ (λ i → rows (F.suc i))

projectᵣ : ∀ {source target} → (Row' source → Row' target) →
  Relation' source → Relation' target
projectᵣ = map

selectᵣ : ∀ {schema} → (Row' schema → Bool) → Relation' schema → Relation' schema
selectᵣ predicate [] = []
selectᵣ predicate (row ∷ rows) with predicate row
... | true = row ∷ selectᵣ predicate rows
... | false = selectᵣ predicate rows

tabulate-cong : ∀ {n schema} (left right : Fin n → Row' schema) →
  (∀ i → left i ≡ right i) → tabulateᵣ left ≡ tabulateᵣ right
tabulate-cong left right same = cong tabulateᵣ (funExt same)

project-tabulate : ∀ {n source target} (project : Row' source → Row' target)
  (rows : Fin n → Row' source) →
  projectᵣ project (tabulateᵣ rows) ≡ tabulateᵣ (λ i → project (rows i))
project-tabulate {zero} project rows = refl
project-tabulate {suc n} project rows =
  cong (project (rows F.zero) ∷_) (project-tabulate project (λ i → rows (F.suc i)))

project-compose : ∀ {source middle target}
  (first : Row' source → Row' middle) (second : Row' middle → Row' target) rows →
  projectᵣ second (projectᵣ first rows) ≡ projectᵣ (λ row → second (first row)) rows
project-compose first second [] = refl
project-compose first second (row ∷ rows) =
  cong (second (first row) ∷_) (project-compose first second rows)

-- A predicate on projected rows can be pushed to the source relation.
select-project : ∀ {source target} (project : Row' source → Row' target)
  (predicate : Row' target → Bool) rows →
  selectᵣ predicate (projectᵣ project rows)
    ≡ projectᵣ project (selectᵣ (λ row → predicate (project row)) rows)
select-project project predicate [] = refl
select-project project predicate (row ∷ rows) with predicate (project row)
... | true = cong (project row ∷_) (select-project project predicate rows)
... | false = select-project project predicate rows
