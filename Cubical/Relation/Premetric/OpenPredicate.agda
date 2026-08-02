module Cubical.Relation.Premetric.OpenPredicate where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open OrderedCommRingTheory ℚOrderedCommRing
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

private
  variable
    ℓA ℓA' ℓB ℓB' ℓP : Level
    A : Type ℓA
    B : Type ℓB

Predicate : (P-ℓ : Level) → Type ℓA → Type (ℓ-max ℓA (ℓ-suc P-ℓ))
Predicate P-ℓ A = A → hProp P-ℓ

fullPredicate : ∀ {A : Type ℓA} {ℓP : Level} → Predicate ℓP A
fullPredicate {ℓP = ℓP} _ = Unit* {ℓ = ℓP} , isPropUnit*

emptyPredicate : ∀ {A : Type ℓA} {ℓP : Level} → Predicate ℓP A
emptyPredicate {ℓP = ℓP} _ = ⊥* {ℓ = ℓP} , isProp⊥*

predicateIntersection : ∀ {A : Type ℓA} {ℓP : Level} →
  Predicate ℓP A → Predicate ℓP A → Predicate ℓP A
predicateIntersection P Q x =
  (fst (P x) × fst (Q x)) , isProp× (snd (P x)) (snd (Q x))

predicatePreimage : ∀ {A : Type ℓA} {B : Type ℓB} {ℓP : Level} →
  (A → B) → Predicate ℓP B → Predicate ℓP A
predicatePreimage f Q x = Q (f x)

module _ (M : PremetricStr ℓA' A) where
  private
    module M = PremetricStr M

  IsOpenPredicate : ∀ {ℓP} → Predicate ℓP A → Type _
  IsOpenPredicate P =
    ∀ x → fst (P x) →
      ∃[ ε ∈ ℚ₊ ] (∀ y → x M.≈[ ε ] y → fst (P y))

  isPropIsOpenPredicate : ∀ {ℓP} (P : Predicate ℓP A) →
    isProp (IsOpenPredicate P)
  isPropIsOpenPredicate P =
    isPropΠ2 λ _ _ → squash₁

  fullPredicateIsOpen : ∀ {ℓP} →
    IsOpenPredicate (fullPredicate {ℓP = ℓP})
  fullPredicateIsOpen x _ =
    ∣ (1 , λ _ _ → tt*) ∣₁

  emptyPredicateIsOpen : ∀ {ℓP} →
    IsOpenPredicate (emptyPredicate {ℓP = ℓP})
  emptyPredicateIsOpen x = ⊥.rec*

  intersectionIsOpen : ∀ {ℓP} (P Q : Predicate ℓP A) →
    IsOpenPredicate P →
    IsOpenPredicate Q →
    IsOpenPredicate (predicateIntersection P Q)
  intersectionIsOpen P Q openP openQ x (x∈P , x∈Q) =
    PT.map2
      (λ (δ , nearP) (ε , nearQ) →
        min₊ δ ε , λ y x≈y →
          nearP y
            (M.isMonotone≈≤ x y (min₊ δ ε) δ
              (ℚ.min≤ (fst δ) (fst ε)) x≈y)
          , nearQ y
            (M.isMonotone≈≤ x y (min₊ δ ε) ε
              (ℚ.min≤' (fst δ) (fst ε)) x≈y))
      (openP x x∈P) (openQ x x∈Q)

  OpenBallPredicate : A → ℚ₊ → Predicate ℓA' A
  OpenBallPredicate centre radius x =
    centre M.≈[ radius ] x , M.isProp≈ centre x radius

  openBallIsOpen : ∀ centre radius →
    IsOpenPredicate (OpenBallPredicate centre radius)
  openBallIsOpen centre radius x centre≈x =
    PT.map openAroundRoundedPoint (M.isRounded≈ centre x radius centre≈x)
    where
    openAroundRoundedPoint :
      Σ[ κ ∈ ℚ₊ ] (κ <₊ radius) × (centre M.≈[ κ ] x) →
      Σ[ δ ∈ ℚ₊ ] (∀ y → x M.≈[ δ ] y → centre M.≈[ radius ] y)
    openAroundRoundedPoint (κ , κ<radius , centre≈κx) =
      gap /2₊ , λ y x≈y →
        M.isMonotone≈< centre y (κ +₊ gap /2₊) radius
          (κ+half-gap<radius)
          (M.isTriangular≈ centre x y κ (gap /2₊) centre≈κx x≈y)
      where
      gap : ℚ₊
      gap = [ radius -₊ κ ]⟨ κ<radius ⟩

      κ+half-gap<radius : (κ +₊ gap /2₊) <₊ radius
      κ+half-gap<radius =
        subst2 ℚ._<_
          (ℚ.+Comm (fst (gap /2₊)) (fst κ))
          (minusPlus₊ radius κ)
          (ℚ.<-+o (fst (gap /2₊)) (fst gap) (fst κ)
            (/2₊<id gap))

module _
  {M : PremetricStr ℓA' A}
  {N : PremetricStr ℓB' B}
  (f : A → B)
  where

  continuousPreimageIsOpen : ∀ {ℓP} (Q : Predicate ℓP B) →
    isContinuous M f N →
    IsOpenPredicate N Q →
    IsOpenPredicate M (predicatePreimage f Q)
  continuousPreimageIsOpen Q continuousF openQ x fx∈Q =
    PT.rec squash₁
      (λ (ε , nearQ) →
        PT.map
          (λ (δ , nearF) →
            δ , λ y x≈y → nearQ (f y) (nearF y x≈y))
          (IsContinuousAt.pres≈ (continuousF x) ε))
      (openQ (f x) fx∈Q)
