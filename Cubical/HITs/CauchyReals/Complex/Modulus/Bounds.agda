module Cubical.HITs.CauchyReals.Complex.Modulus.Bounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Inverse as ℚ using (_⁻¹₊ ; y·[x/y])
open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Archimedean using
  (∃ℚ₊LargerThanℝ₀₊)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition


ComplexScalarBound : ℂ → Type₀
ComplexScalarBound c =
  Σ[ M ∈ ℚ₊ ] modulus c ≤ᵣ rat (fst M)


complexScalarHasRationalBound :
  (c : ℂ) → ∥ ComplexScalarBound c ∥₁
complexScalarHasRationalBound c =
  PT.map
    (λ (M , |c|<M) →
      M , <ᵣWeaken≤ᵣ _ _ |c|<M)
    (∃ℚ₊LargerThanℝ₀₊
      (modulus c , modulusNonNeg c))


boundedModulusProductAtRadius< :
  ∀ c error (M ε : ℚ₊) →
  modulus c ≤ᵣ rat (fst M) →
  modulus error <ᵣ rat (fst ε) →
  modulus c ·ᵣ modulus error
    <ᵣ rat (fst (M ·₊ ε))
boundedModulusProductAtRadius<
  c error M ε |c|≤M |error|<ε =
  isTrans<≡ᵣ _ _ _
    (isTrans≤<ᵣ _ _ _
      (≤ᵣ-·ᵣo
        (modulus c) (rat (fst M)) (modulus error)
        (modulusNonNeg error) |c|≤M)
      (<ᵣ-o·ᵣ
        (modulus error) (rat (fst ε))
        (ℚ₊→ℝ₊ M) |error|<ε))
    (sym (rat·ᵣrat (fst M) (fst ε)))


boundedModulusProduct< :
  ∀ c error (M ε : ℚ₊) →
  modulus c ≤ᵣ rat (fst M) →
  modulus error
    <ᵣ rat (fst ((ℚ._⁻¹₊ M) ·₊ ε)) →
  modulus c ·ᵣ modulus error <ᵣ rat (fst ε)
boundedModulusProduct< c error M ε |c|≤M |error|<η =
  isTrans<≡ᵣ _ _ _
    (isTrans≤<ᵣ _ _ _
      (≤ᵣ-·ᵣo
        (modulus c) (rat (fst M)) (modulus error)
        (modulusNonNeg error) |c|≤M)
      (<ᵣ-o·ᵣ
        (modulus error)
        (rat (fst ((ℚ._⁻¹₊ M) ·₊ ε)))
        (ℚ₊→ℝ₊ M)
        |error|<η))
    (sym
      (rat·ᵣrat
        (fst M) (fst ((ℚ._⁻¹₊ M) ·₊ ε)))
    ∙ cong rat (ℚ.y·[x/y] M (fst ε)))
