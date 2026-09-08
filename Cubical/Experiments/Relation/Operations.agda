{-# OPTIONS --safe --cubical #-}

module Cubical.Experiments.Relation.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base using (Fin)
import Cubical.Data.FinData.Base as F
open import Cubical.Data.FinData.Properties using (discreteFin)
open import Cubical.Data.List.Base using ([]; _∷_; _++_; map)
open import Cubical.Data.Bool using (Bool; true; false; _or_; Dec→Bool; or-assoc; or-comm; or-idem)
open import Cubical.Relation.Nullary using (yes; no)
import Cubical.Data.Empty as Empty
open import Agda.Builtin.String using (String)
open import Cubical.Experiments.Relation.Base using
  (Fields'; Row'; Relation'; Member; selectedFieldType; split; _,,_;
   NonMember; insertField; insert)

-- Ordinary forward application lets relation transformations be read in
-- execution order. It introduces no query syntax or evaluation machinery.
infixl 1 _|>_
_|>_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A → (A → B) → B
value |> transform = transform value

-- Schema-directed lookup reuses Base's field selection and its membership
-- evidence. It does not impose a record-specific accessor on consumers.
get : (name : String) {source : Fields'} → ⦃ member : Member name source ⦄ →
  Row' source → selectedFieldType name {source = source} ⦃ member ⦄
get name {source} ⦃ member ⦄ row with split name {source = source} ⦃ member ⦄ row
... | value ,, rest = value

get-cong : (name : String) {source : Fields'} → ⦃ member : Member name source ⦄ →
  (left right : Row' source) → left ≡ right → get name left ≡ get name right
get-cong name left right same = cong (get name) same

-- Relations retain list order and multiplicity. These operations do not
-- silently deduplicate rows or assume uniqueness of field values.
tabulateᵣ : ∀ {n} {schema : Fields'} → (Fin n → Row' schema) → Relation' schema
tabulateᵣ {zero} rows = []
tabulateᵣ {suc n} rows = rows F.zero ∷ tabulateᵣ (λ i → rows (F.suc i))

projectᵣ : ∀ {source target} → (Row' source → Row' target) →
  Relation' source → Relation' target
projectᵣ = map

deriveᵣ : (name : String) {Ty : Type₀} {source : Fields'} →
  ⦃ fresh : NonMember name source ⦄ → (Row' source → Ty) → Relation' source →
  Relation' (insertField name {Ty = Ty} {source = source})
deriveᵣ name compute = projectᵣ (λ row → insert name (compute row) row)

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

-- Membership of finite keys, insensitive to repeated rows. This is a mask
-- for selection, not an aggregation of the rows' numerical fields.
keyMask : ∀ {n schema} → (Row' schema → Fin n) → Relation' schema → Fin n → Bool
keyMask key [] query = false
keyMask key (row ∷ rows) query =
  Dec→Bool (discreteFin (key row) query) or keyMask key rows query

keyMask-hit : ∀ {n schema} (key : Row' schema → Fin n) row rows →
  keyMask key (row ∷ rows) (key row) ≡ true
keyMask-hit key row rows with discreteFin (key row) (key row)
... | yes same = refl
... | no different = Empty.rec (different refl)

keyMask-project : ∀ {n source target} (project : Row' source → Row' target)
  (key : Row' target → Fin n) rows →
  keyMask key (projectᵣ project rows) ≡ keyMask (λ row → key (project row)) rows
keyMask-project project key [] = refl
keyMask-project project key (row ∷ rows) = funExt (λ query →
  cong (Dec→Bool (discreteFin (key (project row)) query) or_)
    (funExt⁻ (keyMask-project project key rows) query))

keyMask-append : ∀ {n schema} (key : Row' schema → Fin n) left right →
  keyMask key (left ++ right) ≡ (λ query → keyMask key left query or keyMask key right query)
keyMask-append key [] right = refl
keyMask-append key (row ∷ rows) right = funExt (λ query →
  cong (Dec→Bool (discreteFin (key row) query) or_)
    (funExt⁻ (keyMask-append key rows right) query)
  ∙ or-assoc (Dec→Bool (discreteFin (key row) query)) (keyMask key rows query) (keyMask key right query))

keyMask-replay : ∀ {n schema} (key : Row' schema → Fin n) rows →
  keyMask key (rows ++ rows) ≡ keyMask key rows
keyMask-replay key rows = keyMask-append key rows rows
  ∙ funExt (λ query → or-idem (keyMask key rows query))

keyMask-commutes : ∀ {n schema} (key : Row' schema → Fin n) first second →
  keyMask key (first ++ second) ≡ keyMask key (second ++ first)
keyMask-commutes key first second = keyMask-append key first second
  ∙ funExt (λ query → or-comm (keyMask key first query) (keyMask key second query))
  ∙ sym (keyMask-append key second first)
