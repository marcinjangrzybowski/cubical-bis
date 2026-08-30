module Cubical.HITs.PropositionalTruncation.FiniteChoice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool.Base
open import Cubical.Data.FinData.Base using (Fin ; toℕ)
open import Cubical.Data.Nat using (ℕ ; zero)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation.Base
import Cubical.HITs.PropositionalTruncation.Properties as PT

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ
    P : X → Type ℓ'


-- There is always a canonical map in this direction, for every indexing
-- type.  The reverse map is precisely the family-specific choice principle.

propTruncΠ→ΠPropTrunc :
  ∥ ((x : X) → P x) ∥₁ → ((x : X) → ∥ P x ∥₁)
propTruncΠ→ΠPropTrunc =
  PT.rec (isPropΠ λ _ → squash₁)
    (λ section x → ∣ section x ∣₁)


PropTruncChoiceFor :
  (X : Type ℓ) → (X → Type ℓ') → Type (ℓ-max ℓ ℓ')
PropTruncChoiceFor X P =
  ((x : X) → ∥ P x ∥₁) → ∥ ((x : X) → P x) ∥₁


choiceFor→propTruncΠ≃ΠPropTrunc :
  PropTruncChoiceFor X P →
  ∥ ((x : X) → P x) ∥₁ ≃ ((x : X) → ∥ P x ∥₁)
choiceFor→propTruncΠ≃ΠPropTrunc choice =
  propBiimpl→Equiv
    squash₁
    (isPropΠ λ _ → squash₁)
    propTruncΠ→ΠPropTrunc
    choice


propTruncΠ≃ΠPropTrunc→choiceFor :
  (∥ ((x : X) → P x) ∥₁ ≃ ((x : X) → ∥ P x ∥₁)) →
  PropTruncChoiceFor X P
propTruncΠ≃ΠPropTrunc→choiceFor = invEq


-- A Bool-indexed dependent function is exactly a pair.  The chosen order is
-- false, then true.  Product commutativity is therefore unnecessary: using
-- the same order before and after truncation makes the factors line up.

ΠBoolIso× : {P : Bool → Type ℓ} →
  Iso ((b : Bool) → P b) (P false × P true)
ΠBoolIso× .Iso.fun section = section false , section true
ΠBoolIso× .Iso.inv (pfalse , ptrue) false = pfalse
ΠBoolIso× .Iso.inv (pfalse , ptrue) true = ptrue
ΠBoolIso× .Iso.sec _ = refl
ΠBoolIso× .Iso.ret section =
  funExt λ where
    false → refl
    true → refl


ΠBoolEquiv× : {P : Bool → Type ℓ} →
  ((b : Bool) → P b) ≃ (P false × P true)
ΠBoolEquiv× = isoToEquiv ΠBoolIso×


-- This is the product factorization suggested in the question:
--
--   ∥ Π b , P b ∥
--     ≃ ∥ P false × P true ∥
--     ≃ ∥ P false ∥ × ∥ P true ∥
--     ≃ Π b , ∥ P b ∥.

propTruncΠBool≃ΠBoolPropTrunc : {P : Bool → Type ℓ} →
  ∥ ((b : Bool) → P b) ∥₁ ≃ ((b : Bool) → ∥ P b ∥₁)
propTruncΠBool≃ΠBoolPropTrunc {P = P} =
    PT.propTrunc≃ (ΠBoolEquiv× {P = P})
  ⋆ invEquiv PT.∥∥-×-≃
  ⋆ invEquiv (ΠBoolEquiv× {P = λ b → ∥ P b ∥₁})


boolChoice : {P : Bool → Type ℓ} →
  ((b : Bool) → ∥ P b ∥₁) → ∥ ((b : Bool) → P b) ∥₁
boolChoice = invEq propTruncΠBool≃ΠBoolPropTrunc


-- The non-dependent specialization is the equivalence from the question.

propTruncBoolFunction≃BoolFunctionPropTrunc : {Y : Type ℓ} →
  ∥ (Bool → Y) ∥₁ ≃ (Bool → ∥ Y ∥₁)
propTruncBoolFunction≃BoolFunctionPropTrunc {Y = Y} =
  propTruncΠBool≃ΠBoolPropTrunc {P = λ _ → Y}


-- The same phenomenon holds for every finite `Fin n`-indexed dependent
-- family.  `PT.recFin` performs the finite number of truncation eliminations;
-- it does not invoke any choice axiom.

finChoice : {n : ℕ} {P : Fin n → Type ℓ} →
  ((i : Fin n) → ∥ P i ∥₁) → ∥ ((i : Fin n) → P i) ∥₁
finChoice = PT.recFin squash₁ ∣_∣₁


propTruncΠFin≃ΠFinPropTrunc : {n : ℕ} {P : Fin n → Type ℓ} →
  ∥ ((i : Fin n) → P i) ∥₁ ≃ ((i : Fin n) → ∥ P i ∥₁)
propTruncΠFin≃ΠFinPropTrunc =
  propBiimpl→Equiv
    squash₁
    (isPropΠ λ _ → squash₁)
    propTruncΠ→ΠPropTrunc
    finChoice


-- For a constant family over an inhabited indexing type there is no choice
-- issue, finite or otherwise.  Evaluation at the chosen point and constant
-- functions show that both sides are just `∥ Y ∥₁`.

functionIntoPropTrunc≃PropTrunc :
  (x₀ : X) {Y : Type ℓ'} → (X → ∥ Y ∥₁) ≃ ∥ Y ∥₁
functionIntoPropTrunc≃PropTrunc x₀ =
  propBiimpl→Equiv
    (isPropΠ λ _ → squash₁)
    squash₁
    (λ section → section x₀)
    (λ y _ → y)


propTruncFunction≃PropTrunc :
  (x₀ : X) {Y : Type ℓ'} → ∥ (X → Y) ∥₁ ≃ ∥ Y ∥₁
propTruncFunction≃PropTrunc x₀ =
  propBiimpl→Equiv
    squash₁ squash₁
    (PT.map (λ section → section x₀))
    (PT.map (λ y _ → y))


propTruncFunction≃FunctionPropTrunc :
  (x₀ : X) {Y : Type ℓ'} →
  ∥ (X → Y) ∥₁ ≃ (X → ∥ Y ∥₁)
propTruncFunction≃FunctionPropTrunc x₀ =
    propTruncFunction≃PropTrunc x₀
  ⋆ invEquiv (functionIntoPropTrunc≃PropTrunc x₀)


propTruncNatFunction≃NatFunctionPropTrunc : {Y : Type ℓ} →
  ∥ (ℕ → Y) ∥₁ ≃ (ℕ → ∥ Y ∥₁)
propTruncNatFunction≃NatFunctionPropTrunc =
  propTruncFunction≃FunctionPropTrunc zero


natTruncatedValues→truncatedConstantFunction : {Y : Type ℓ} →
  (ℕ → ∥ Y ∥₁) → ∥ (ℕ → Y) ∥₁
natTruncatedValues→truncatedConstantFunction values =
  PT.map (λ y _ → y) (values zero)


-- For a genuinely dependent family, the missing reverse map is countable
-- choice.  Without it, all finite prefixes can still be chosen merely.

CountableChoiceFor :
  (P : ℕ → Type ℓ) → Type ℓ
CountableChoiceFor P = PropTruncChoiceFor ℕ P


countableChoiceFor→propTruncΠNat≃ΠNatPropTrunc :
  {P : ℕ → Type ℓ} → CountableChoiceFor P →
  ∥ ((n : ℕ) → P n) ∥₁ ≃ ((n : ℕ) → ∥ P n ∥₁)
countableChoiceFor→propTruncΠNat≃ΠNatPropTrunc =
  choiceFor→propTruncΠ≃ΠPropTrunc


propTruncΠNat≃ΠNatPropTrunc→countableChoiceFor :
  {P : ℕ → Type ℓ} →
  (∥ ((n : ℕ) → P n) ∥₁ ≃ ((n : ℕ) → ∥ P n ∥₁)) →
  CountableChoiceFor P
propTruncΠNat≃ΠNatPropTrunc→countableChoiceFor =
  propTruncΠ≃ΠPropTrunc→choiceFor


NatPrefix : (ℕ → Type ℓ) → ℕ → Type ℓ
NatPrefix P k = (i : Fin k) → P (toℕ i)


finitePrefixChoice : {P : ℕ → Type ℓ} →
  ((n : ℕ) → ∥ P n ∥₁) →
  (k : ℕ) → ∥ NatPrefix P k ∥₁
finitePrefixChoice choices k =
  finChoice (λ i → choices (toℕ i))
