module Cubical.Experiments.Relation.Base where

open import Cubical.Data.List
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Agda.Builtin.String


_==S_ = primStringEquality

_≡S_ : String → String → Type
x ≡S x' = Bool→Type (x ==S x')


infixr 30 _∶_,_
infixl 40 _∶_]

data Fields' : Type₁ where
  [] : Fields'
  _∶_,_ : String → Type → Fields' → Fields'

pattern _∶_] name Ty = name ∶ Ty , []


private
  containsName : String → Fields' → Bool
  containsName name [] = false
  containsName name (current ∶ _ , fields) =
    (name ==S current) or containsName name fields

  containsString : String → List String → Bool
  containsString name [] = false
  containsString name (current ∷ names) =
    (name ==S current) or containsString name names

  insertUnique : String → List String → List String
  insertUnique name names =
    if containsString name names then names else name ∷ names


-- Produce the list of duplicated names in a schema.
nonUniqNames : Fields' → List String
nonUniqNames [] = []
nonUniqNames (name ∶ _ , fields) =
  if containsName name fields
  then insertUnique name (nonUniqNames fields)
  else nonUniqNames fields

opaque
  DuplicatedNames∶ : List String → Type
  DuplicatedNames∶ _ = ⊥

UniqNames : List String → Type
UniqNames [] = Unit
UniqNames names@(_ ∷ _) = DuplicatedNames∶ names

record Fields : Type₁ where
  constructor [_
  field
    fields : Fields'
    {uniq} : UniqNames (nonUniqNames fields)

f1 : Fields
f1 = [ "A" ∶ ℕ , "B" ∶ ℤ , "C" ∶ Bool ]


infixr 30 _,,_
infixl 40 _⟩

data Row' : Fields' → Type₁ where
  [] : Row' []
  _,,_ : ∀ {name Ty fields}
    → Ty → Row' fields → Row' (name ∶ Ty , fields)

pattern _⟩ value = value ,, []

record Row (schema : Fields) : Type₁ where
  constructor ⟨_
  open Fields schema

  field
    row : Row' fields


Relation' : Fields' → Type₁
Relation' = List ∘ Row'

Relation ⟦_⟧ : Fields → Type₁
Relation = Relation' ∘ Fields.fields
⟦_⟧ = Relation


-- Curried functions whose arguments are described by a schema.
F'→ : ∀ {ℓ} → Fields' → Type ℓ → Type ℓ
F'→ [] result = result
F'→ (_ ∶ Ty , fields) result = Ty → F'→ fields result

_⟶_ : Fields → Fields → Type₁
source ⟶ target = F'→ (Fields.fields source) ⟦ target ⟧

applyRow : ∀ {ℓ} {fields : Fields'} {result : Type ℓ}
  → F'→ fields result → Row' fields → result
applyRow {fields = []} function [] = function
applyRow {fields = _ ∶ _ , _} function (value ,, row) =
  applyRow (function value) row

mapᵣ : ∀ {source target}
  → source ⟶ target → ⟦ source ⟧ → ⟦ target ⟧
mapᵣ operation rows =
  foldr _++_ [] (map (applyRow operation) rows)


-- Decidable predicates on field names.

data So : Bool → Type where
  holds : So true

instance
  autoSo : So true
  autoSo = holds

memberName : String → Fields' → Bool
memberName = containsName

noCommonNames : Fields' → Fields' → Bool
noCommonNames [] right = true
noCommonNames (name ∶ _ , left) right =
  not (containsName name right) and noCommonNames left right

multipleFields : Fields' → Bool
multipleFields [] = false
multipleFields (_ ∶ _ , []) = false
multipleFields (_ ∶ _ , _ ∶ _ , _) = true

Member : String → Fields' → Type
Member name fields = So (memberName name fields)

NonMember : String → Fields' → Type
NonMember name fields = So (not (memberName name fields))

NoCommonNames : Fields' → Fields' → Type
NoCommonNames left right = So (noCommonNames left right)

MultipleFields : Fields' → Type
MultipleFields fields = So (multipleFields fields)


-- Operations on schemas and rows.

private
  concatFieldsRaw : Fields' → Fields' → Fields'
  concatFieldsRaw [] right = right
  concatFieldsRaw (name ∶ Ty , left) right =
    name ∶ Ty , concatFieldsRaw left right

  concatRowsRaw : ∀ {left right}
    → Row' left → Row' right → Row' (concatFieldsRaw left right)
  concatRowsRaw [] right = right
  concatRowsRaw (value ,, left) right =
    value ,, concatRowsRaw left right

  record FieldSelection (name : String) (source : Fields') : Type₁ where
    constructor selection
    field
      selectedType : Type
      remainingFields : Fields'
      removeSelected : Row' source → Row' remainingFields
      splitSelected :
        Row' source → Row' (name ∶ selectedType , remainingFields)

  open FieldSelection

  prependSelection : ∀ {name current Ty rest}
    → FieldSelection name rest
    → FieldSelection name (current ∶ Ty , rest)
  prependSelection {name = name} {current = current} {Ty = Ty} tail =
    selection
      (selectedType tail)
      (current ∶ Ty , remainingFields tail)
      removeHere
      splitHere
    where
    removeHere :
      Row' (current ∶ Ty , _)
      → Row' (current ∶ Ty , remainingFields tail)
    removeHere (value ,, row) = value ,, removeSelected tail row

    splitHere :
      Row' (current ∶ Ty , _)
      → Row'
          (name ∶ selectedType tail ,
           current ∶ Ty , remainingFields tail)
    splitHere (value ,, row) with splitSelected tail row
    ... | selected ,, remaining = selected ,, value ,, remaining

  selectionFrom : (name : String) (source : Fields')
    → ⦃ member : Member name source ⦄
    → FieldSelection name source
  selectionFrom name [] ⦃ () ⦄
  selectionFrom name (current ∶ Ty , rest) ⦃ member ⦄
    with name ==S current
  ... | true =
    selection Ty rest
      (λ { (_ ,, row) → row })
      (λ { (value ,, row) → value ,, row })
  ... | false =
    prependSelection (selectionFrom name rest ⦃ member ⦄)


concatFields : (left right : Fields')
  → ⦃ disjoint : NoCommonNames left right ⦄
  → Fields'
concatFields left right = concatFieldsRaw left right

concat : ∀ {left right}
  → ⦃ disjoint : NoCommonNames left right ⦄
  → Row' left → Row' right → Row' (concatFields left right)
concat = concatRowsRaw

selectedFieldType : (name : String) {source : Fields'}
  → ⦃ member : Member name source ⦄
  → Type
selectedFieldType name {source = source} ⦃ member ⦄ =
  FieldSelection.selectedType
    (selectionFrom name source ⦃ member ⦄)

removeField : (name : String) {source : Fields'}
  → ⦃ member : Member name source ⦄
  → Fields'
removeField name {source = source} ⦃ member ⦄ =
  FieldSelection.remainingFields
    (selectionFrom name source ⦃ member ⦄)

remove : (name : String) {source : Fields'}
  → ⦃ member : Member name source ⦄
  → Row' source → Row' (removeField name {source = source})
remove name {source = source} ⦃ member ⦄ =
  FieldSelection.removeSelected
    (selectionFrom name source ⦃ member ⦄)

splitField : (name : String) {source : Fields'}
  → ⦃ member : Member name source ⦄
  → Fields'
splitField name {source = source} ⦃ member ⦄ =
  name ∶ FieldSelection.selectedType selected ,
  FieldSelection.remainingFields selected
  where
  selected = selectionFrom name source ⦃ member ⦄

split : (name : String) {source : Fields'}
  → ⦃ member : Member name source ⦄
  → Row' source → Row' (splitField name {source = source})
split name {source = source} ⦃ member ⦄ =
  FieldSelection.splitSelected
    (selectionFrom name source ⦃ member ⦄)

insertField : (name : String) {Ty : Type} {source : Fields'}
  → ⦃ fresh : NonMember name source ⦄
  → Fields'
insertField name {Ty = Ty} {source = source} = name ∶ Ty , source

insert : (name : String) {Ty : Type} {source : Fields'}
  → ⦃ fresh : NonMember name source ⦄
  → Ty → Row' source → Row' (insertField name)
insert _ value row = value ,, row


-- Lifts to relations.

concatᵣ : ∀ {left right}
  → ⦃ disjoint : NoCommonNames left right ⦄
  → Relation' left → Relation' right
  → Relation' (concatFields left right)
concatᵣ {left = left} {right = right} leftRows rightRows =
  foldr _++_ []
    (map (λ leftRow →
      map (concatRowsRaw {left = left} {right = right} leftRow) rightRows)
      leftRows)

removeᵣ : (name : String) {source : Fields'}
  → ⦃ member : Member name source ⦄
  → Relation' source → Relation' (removeField name {source = source})
removeᵣ name {source = source} ⦃ member ⦄ =
  map (FieldSelection.removeSelected
    (selectionFrom name source ⦃ member ⦄))

splitᵣ : (name : String) {source : Fields'}
  → ⦃ member : Member name source ⦄
  → Relation' source → Relation' (splitField name {source = source})
splitᵣ name {source = source} ⦃ member ⦄ =
  map (FieldSelection.splitSelected
    (selectionFrom name source ⦃ member ⦄))

insertᵣ : (name : String) {Ty : Type} {source : Fields'}
  → ⦃ fresh : NonMember name source ⦄
  → Ty → Relation' source → Relation' (insertField name)
insertᵣ name value = map (insert name value)
