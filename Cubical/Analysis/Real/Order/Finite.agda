module Cubical.Analysis.Real.Order.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Data.FinData as Fin using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup)
open import Cubical.Data.Sum as Sum
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊; /2₊<id)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Located

private
  positiveSlack : ∀ x ε → x <ℝ x + rat (fst ε)
  positiveSlack x ε = subst (_<ℝ x + rat (fst ε)) (addIdR x)
    (<ℝ-addL 0ℝ (rat (fst ε)) x (<ℚ→<ℝ 0 (fst ε) (snd ε)))

-- Finite near-maximizers exist even when comparing coefficients exactly is
-- undecidable. The selected index remains truncated at the given accuracy.
ApproximateMaximum : ∀ {n} → Vec ℝ n → ℚ₊ → Type₀
ApproximateMaximum {n} values ε =
  ∥ Σ[ i ∈ Fin n ] (∀ j → lookup j values <ℝ lookup i values + rat (fst ε)) ∥₁

finiteApproximateMaximum : ∀ {n} (values : Vec ℝ (suc n)) ε → ApproximateMaximum values ε
finiteApproximateMaximum (x ∷ []) ε = ∣ zero , (λ { zero → positiveSlack x ε ; (suc ()) }) ∣₁
finiteApproximateMaximum (x ∷ y ∷ tail) ε = PT.rec squash₁ choose
  (finiteApproximateMaximum (y ∷ tail) (ε /2₊))
  where
  values = y ∷ tail
  δ = rat (fst (ε /2₊))

  smaller : δ <ℝ rat (fst ε)
  smaller = <ℚ→<ℝ (fst (ε /2₊)) (fst ε) (/2₊<id ε)

  choose : (Σ[ i ∈ Fin _ ] (∀ j → lookup j values <ℝ lookup i values + δ)) →
    ApproximateMaximum (x ∷ values) ε
  choose (i , maximal) = PT.rec squash₁ (Sum.rec keepTail keepHead)
    (dichotomyℝ selected x (selected + δ) (positiveSlack selected (ε /2₊)))
    where
    selected = lookup i values

    keepTail : x <ℝ selected + δ → ApproximateMaximum (x ∷ values) ε
    keepTail less = ∣ suc i , (λ
      { zero → <ℝ-trans x (selected + δ) (selected + rat (fst ε)) less
          (<ℝ-addL δ (rat (fst ε)) selected smaller)
      ; (suc j) → <ℝ-trans (lookup j values) (selected + δ) (selected + rat (fst ε))
          (maximal j) (<ℝ-addL δ (rat (fst ε)) selected smaller) }) ∣₁

    keepHead : selected <ℝ x → ApproximateMaximum (x ∷ values) ε
    keepHead less = ∣ zero , (λ
      { zero → positiveSlack x ε
      ; (suc j) → <ℝ-trans (lookup j values) (selected + δ) (x + rat (fst ε))
          (maximal j) (<ℝ-add selected x δ (rat (fst ε)) less smaller) }) ∣₁
