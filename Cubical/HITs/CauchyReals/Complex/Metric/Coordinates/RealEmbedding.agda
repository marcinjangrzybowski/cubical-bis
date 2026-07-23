module Cubical.HITs.CauchyReals.Complex.Metric.Coordinates.RealEmbedding where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Premetric.Mappings

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Metric.Base

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


opaque
  fromℝ-difference-path : ∀ x y →
    fromℝ x -ℂ fromℝ y ≡ fromℝ (x -ᵣ y)
  fromℝ-difference-path x y = ℂ≡ refl ℝ!


opaque
  modulus-fromℝ-difference : ∀ x y →
    modulus (fromℝ x -ℂ fromℝ y) ≡ absᵣ (x -ᵣ y)
  modulus-fromℝ-difference x y =
    cong modulus (fromℝ-difference-path x y) ∙ modulus-fromℝ (x -ᵣ y)


opaque
  real-difference-close : ∀ x y ε → x ≈ℝ[ ε ] y →
    absᵣ (x -ᵣ y) <ᵣ rat (fst ε)
  real-difference-close x y ε x≈y =
    fst (∼≃abs<ε x y ε) (≈ℝ→∼ x y ε x≈y)


opaque
  fromℝ-difference-close : ∀ x y ε → x ≈ℝ[ ε ] y →
    modulus (fromℝ x -ℂ fromℝ y) <ᵣ rat (fst ε)
  fromℝ-difference-close x y ε x≈y = subst (_<ᵣ rat (fst ε))
    (sym (modulus-fromℝ-difference x y))
    (real-difference-close x y ε x≈y)


opaque
  fromℝ-pres≈ : ∀ x y ε → x ≈ℝ[ ε ] y → fromℝ x ≈ℂ[ ε ] fromℝ y
  fromℝ-pres≈ = fromℝ-difference-close


fromℝIsNonExpanding :
  IsNonExpanding (snd ℝPremetricSpace) fromℝ (snd ℂPremetricSpace)
IsNonExpanding.pres≈ fromℝIsNonExpanding = fromℝ-pres≈


fromℝNE : NE[ ℝPremetricSpace , ℂPremetricSpace ]
fromℝNE = fromℝ , fromℝIsNonExpanding
