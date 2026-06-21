{-

ℚ is a Field

-}
module Cubical.Algebra.Field.Instances.Rationals where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.Field

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Int.Fast as ℤ
  using (ℤ; pos; negsuc; ℕ₊₁→ℤ; isSetℤ; 0≢1-ℤ)
  renaming (_·_ to _·ℤ_; -_ to -ℤ_)
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals as ℚ
open import Cubical.Data.Sigma
open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.HITs.SetQuotients as SetQuotients

open import Cubical.Relation.Nullary

open CommRingStr (ℚCommRing .snd)
open Units        ℚCommRing

0≢1-ℚ : ¬ Path ℚ 0 1
0≢1-ℚ p = 0≢1-ℤ (effective (λ _ _ → isSetℤ _ _) isEquivRel∼ _ _ p)

a/b≡0→a≡0 : (x : ℤ × ℕ₊₁) → [ x ] ≡ 0 → x .fst ≡ 0
a/b≡0→a≡0 (a , b) a/b≡0 =
  sym (ℤ.·IdR a) ∙ a·1≡0·b ∙ ℤ.·AnnihilL (ℕ₊₁→ℤ b)
  where
  a·1≡0·b : a ·ℤ 1 ≡ 0 ·ℤ (ℕ₊₁→ℤ b)
  a·1≡0·b = effective (λ _ _ → isSetℤ _ _) isEquivRel∼ _ _ a/b≡0

a≡0→a/b≡0 : (x : ℤ × ℕ₊₁) → x .fst ≡ 0 → [ x ] ≡ 0
a≡0→a/b≡0 (a , b) a≡0 = eq/ _ _ a·1≡0·b
  where
  a·1≡0·b : a ·ℤ 1 ≡ 0 ·ℤ (ℕ₊₁→ℤ b)
  a·1≡0·b = (λ i → a≡0 i ·ℤ 1) ∙ ℤ.·AnnihilL (ℕ₊₁→ℤ b)

hasInverseℚ : (q : ℚ) → ¬ q ≡ 0 → Σ[ p ∈ ℚ ] q ℚ.· p ≡ 1
hasInverseℚ = SetQuotients.elimProp
  (λ q → isPropΠ (λ _ → inverseUniqueness q))
  (λ x x≢0 →
    let a≢0 = λ a≡0 → x≢0 (a≡0→a/b≡0 x a≡0)
    in inv-helper x a≢0 , inv·-helper x a≢0)
  where
  inv-helper : (x : ℤ × ℕ₊₁) → ¬ x .fst ≡ 0 → ℚ
  inv-helper (pos zero , _) a≢0 = Empty.rec (a≢0 refl)
  inv-helper (pos (suc a) , b) _ = [ ℕ₊₁→ℤ b , 1+ a ]
  inv-helper (negsuc a , b) _ = [ -ℤ ℕ₊₁→ℤ b , 1+ a ]

  inv·-helper : (x : ℤ × ℕ₊₁) (a≢0 : ¬ x .fst ≡ 0) → [ x ] ℚ.· inv-helper x a≢0 ≡ 1
  inv·-helper (pos zero , b) a≢0 = Empty.rec (a≢0 refl)
  inv·-helper (pos (suc a) , b) _ = eq/ _ _ ℤ!
  inv·-helper (negsuc a , b) _ = eq/ _ _ ℤ!

ℚField : Field ℓ-zero
ℚField = makeFieldFromCommRing ℚCommRing hasInverseℚ 0≢1-ℚ

_[_]⁻¹ : (x : ℚ) → ¬ x ≡ 0 → ℚ
_[_]⁻¹ = FieldStr._[_]⁻¹ $ snd ℚField

_/_[_] : ℚ → (y : ℚ) → ¬ y ≡ 0 → ℚ
x / y [ p ] = x ℚ.· (y [ p ]⁻¹)
