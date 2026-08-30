module Cubical.Analysis.Real.Order.Apartness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Rationals.Base using (ℚ)
import Cubical.Data.Rationals.Order as ℚOrder

open import Cubical.Relation.Binary.Order.Apartness.Base
  using (IsApartness; Apartness; isapartness; apartness)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Analysis.Real.Base using (ℝ; rat; isSetℝ)
open import Cubical.Analysis.Real.Algebra.Negation using (-_)
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
  using (<ℚ→<ℝ; <ℝ→<ℚ)
open import Cubical.Analysis.Real.Order.Strict.Properties
  using (<ℝ-irrefl; <ℝ-asym)
open import Cubical.Analysis.Real.Order.Strict.Addition
  using (<ℝ-addR; <ℝ-addR-cancel; <ℝ-neg)
open import Cubical.Analysis.Real.Order.Strict.Located
  using (dichotomyℝ)


infix 4 _#ℝ_

_#ℝ_ : ℝ → ℝ → Type₀
x #ℝ y = (x <ℝ y) ⊎ (y <ℝ x)

isProp#ℝ : ∀ x y → isProp (x #ℝ y)
isProp#ℝ x y =
  isProp⊎ (isProp<ℝ x y) (isProp<ℝ y x) (<ℝ-asym x y)

apartSym : ∀ x y → x #ℝ y → y #ℝ x
apartSym x y = ⊎.rec inr inl

apartIrrefl : ∀ x → ¬ x #ℝ x
apartIrrefl x = ⊎.rec (<ℝ-irrefl x) (<ℝ-irrefl x)

apartCotrans : ∀ x y z →
  x #ℝ y → ∥ (x #ℝ z) ⊎ (y #ℝ z) ∥₁
apartCotrans x y z = ⊎.rec x<yCase y<xCase
  where
  x<yCase : x <ℝ y → ∥ (x #ℝ z) ⊎ (y #ℝ z) ∥₁
  x<yCase x<y = PT.map
    (⊎.rec (λ z<y → inr (inr z<y))
           (λ x<z → inl (inl x<z)))
    (dichotomyℝ x z y x<y)

  y<xCase : y <ℝ x → ∥ (x #ℝ z) ⊎ (y #ℝ z) ∥₁
  y<xCase y<x = PT.map
    (⊎.rec (λ z<x → inl (inr z<x))
           (λ y<z → inr (inl y<z)))
    (dichotomyℝ y z x y<x)

isApartnessℝ : IsApartness _#ℝ_
isApartnessℝ = isapartness
  isSetℝ isProp#ℝ apartIrrefl apartCotrans apartSym

ℝApartness : Apartness ℓ-zero ℓ-zero
ℝApartness = apartness ℝ _#ℝ_ isApartnessℝ

apart→notEqual : ∀ x y → x #ℝ y → ¬ x ≡ y
apart→notEqual x y x#y x≡y =
  apartIrrefl x (subst (x #ℝ_) (sym x≡y) x#y)

rat#rat≃ : ∀ p q →
  (rat p #ℝ rat q) ≃ (p ℚOrder.# q)
rat#rat≃ p q = propBiimpl→Equiv
  (isProp#ℝ (rat p) (rat q)) (ℚOrder.isProp# p q)
  (⊎.map (<ℝ→<ℚ p q) (<ℝ→<ℚ q p))
  (⊎.map (<ℚ→<ℝ p q) (<ℚ→<ℝ q p))

apartAddR : ∀ x y z →
  x #ℝ y → x + z #ℝ y + z
apartAddR x y z =
  ⊎.map (<ℝ-addR x y z) (<ℝ-addR y x z)

apartAddR-cancel : ∀ x y z →
  x + z #ℝ y + z → x #ℝ y
apartAddR-cancel x y z =
  ⊎.map (<ℝ-addR-cancel x y z) (<ℝ-addR-cancel y x z)

addRApartEquiv : ∀ x y z →
  (x + z #ℝ y + z) ≃ (x #ℝ y)
addRApartEquiv x y z = propBiimpl→Equiv
  (isProp#ℝ (x + z) (y + z)) (isProp#ℝ x y)
  (apartAddR-cancel x y z) (apartAddR x y z)

apartNeg : ∀ x y → x #ℝ y → (- x) #ℝ (- y)
apartNeg x y = ⊎.rec
  (λ x<y → inr (<ℝ-neg x y x<y))
  (λ y<x → inl (<ℝ-neg y x y<x))
