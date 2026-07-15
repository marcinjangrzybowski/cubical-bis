module Cubical.HITs.CauchyReals.Exponentiation.RealPower.NonzeroRealGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool
open import Cubical.Data.Sigma

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Infrastructure

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

private
  positiveSignGroupIso : GroupIso (DirProd ·₊Groupℝ BoolGroup) ·Groupℝ
  positiveSignGroupIso .fst = invIso Iso-ℝ₋₊-ℝ₊×𝟚
  positiveSignGroupIso .snd = makeIsGroupHom preservesMultiplication
    where
    preservesMultiplication : (x y : ℝ₊ × Bool) →
      ℝ₊×Bool→ℝ₋₊
        (GroupStr._·_ (snd (DirProd ·₊Groupℝ BoolGroup)) x y)
      ≡ ℝ₊×Bool→ℝ₋₊ x ·ᵣ₋₊ ℝ₊×Bool→ℝ₋₊ y
    preservesMultiplication (x , false) (y , false) = ℝ₋₊≡ Simpleℝ.solve!
    preservesMultiplication (x , false) (y , true) = ℝ₋₊≡ Simpleℝ.solve!
    preservesMultiplication (x , true) (y , false) = ℝ₋₊≡ Simpleℝ.solve!
    preservesMultiplication (x , true) (y , true) = ℝ₋₊≡ Simpleℝ.solve!

-- Previous name: GroupIso-ℝˣ-ℝˣ₊×𝟚.
nonzeroRealGroupIso : GroupIso ·Groupℝ (DirProd ·₊Groupℝ BoolGroup)
nonzeroRealGroupIso = invGroupIso positiveSignGroupIso
