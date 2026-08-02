module Cubical.HITs.CauchyRealsP.Foundation.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Int.Fast using (pos; neg)
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyRealsP.Foundation.Rationals

open import Cubical.Relation.Premetric.Completion.Base ℚPremetricSpace public
  renaming
    ( ℭ     to ℝ
    ; ι     to rat
    ; eqℭ   to eqℝ
    ; ι-ι   to rat-rat
    ; ι-lim to rat-lim
    ; lim-ι to lim-rat
    )

-- Keep the generic elimination principles visible.  Their `ℭ` names make
-- their origin explicit even though their carrier is specialised to ℝ here.
open import Cubical.Relation.Premetric.Completion.Elim ℚPremetricSpace public

_∼[_]ₚ_ : ℝ → ℚ₊ → ℝ → hProp ℓ-zero
x ∼[ ε ]ₚ y = x ∼[ ε ] y , isProp∼ _ _ _

rat-rat-fromAbs : ∀ q r ε
  → abs (q ℚ.- r) ℚ.< ⟨ ε ⟩₊
  → rat q ∼[ ε ] rat r
rat-rat-fromAbs q r ε = rat-rat q r ε

instance
  fromNatℝ : HasFromNat ℝ
  fromNatℝ .HasFromNat.Constraint _ = Unit
  fromNatℝ .HasFromNat.fromNat n = rat [ pos n / 1 ]

  fromNegℝ : HasFromNeg ℝ
  fromNegℝ .HasFromNeg.Constraint _ = Unit
  fromNegℝ .HasFromNeg.fromNeg n = rat [ neg n / 1 ]
