open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Base

module Cubical.Analysis.Complex.FundamentalTheorem.Completion.FiniteMatching
  (M : PremetricSpace ℓ-zero ℓ-zero) where

-- Matching uses a bijection of the finite index sets, so repeated points
-- retain their multiplicities. All permutation witnesses stay truncated.

open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Rationals.Order as Q
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; _+₊_; _<₊_; _≤₊_; max₊; max₊LUB<)
open PositiveRationals.PositiveHalvesℚ using (_/2₊; /2₊<id)

private module P = PremetricStr (snd M)

Match : ∀ {n} → Vec (fst M) n → ℚ₊ → Vec (fst M) n → Type₀
Match {n} xs ε ys = PT.∥ Σ[ σ ∈ (Fin n ≃ Fin n) ]
  (∀ i → lookup i xs P.≈[ ε ] lookup (equivFun σ i) ys) ∥₁

match-refl : ∀ {n} (xs : Vec (fst M) n) ε → Match xs ε xs
match-refl {n} xs ε = PT.∣ idEquiv (Fin n) , (λ i → P.isRefl≈ (lookup i xs) ε) ∣₁

match-sym : ∀ {n} (xs ys : Vec (fst M) n) ε → Match xs ε ys → Match ys ε xs
match-sym xs ys ε = PT.map λ { (σ , close) → invEquiv σ , λ i →
  subst (λ j → lookup j ys P.≈[ ε ] lookup (invEq σ i) xs) (secEq σ i)
    (P.isSym≈ (lookup (invEq σ i) xs) (lookup (equivFun σ (invEq σ i)) ys) ε
      (close (invEq σ i))) }

match-triangle : ∀ {n} (xs ys zs : Vec (fst M) n) ε δ →
  Match xs ε ys → Match ys δ zs → Match xs (ε +₊ δ) zs
match-triangle xs ys zs ε δ = PT.map2 λ { (σ , xy) (ρ , yz) →
  compEquiv σ ρ , λ i → P.isTriangular≈
    (lookup i xs) (lookup (equivFun σ i) ys) (lookup (equivFun ρ (equivFun σ i)) zs)
    ε δ (xy i) (yz (equivFun σ i)) }

match-monotone : ∀ {n} (xs ys : Vec (fst M) n) ε δ →
  ε ≤₊ δ → Match xs ε ys → Match xs δ ys
match-monotone xs ys ε δ below = PT.map λ { (σ , close) → σ , λ i →
  P.isMonotone≈≤ (lookup i xs) (lookup (equivFun σ i) ys) ε δ below (close i) }

-- A finite collection of open inequalities has a common smaller radius.
-- Only finitely many truncations are eliminated; no modulus is selected.
finite-rounded : ∀ n (f g : Fin n → fst M) ε →
  (∀ i → f i P.≈[ ε ] g i) →
  PT.∥ Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) × (∀ i → f i P.≈[ δ ] g i) ∥₁
finite-rounded zero f g ε close = PT.∣ ε /2₊ , /2₊<id ε , (λ ()) ∣₁
finite-rounded (suc n) f g ε close = PT.map2 combine
  (P.isRounded≈ (f zero) (g zero) ε (close zero))
  (finite-rounded n (λ i → f (suc i)) (λ i → g (suc i)) ε (λ i → close (suc i)))
  where
  combine :
    (Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) × (f zero P.≈[ δ ] g zero)) →
    (Σ[ η ∈ ℚ₊ ] (η <₊ ε) × (∀ i → f (suc i) P.≈[ η ] g (suc i))) →
    Σ[ κ ∈ ℚ₊ ] (κ <₊ ε) × (∀ i → f i P.≈[ κ ] g i)
  combine (δ , δ<ε , head) (η , η<ε , tail) =
    max₊ δ η , max₊LUB< δ η ε δ<ε η<ε , λ
      { zero → P.isMonotone≈≤ (f zero) (g zero) δ (max₊ δ η)
          (Q.≤max (fst δ) (fst η)) head
      ; (suc i) → P.isMonotone≈≤ (f (suc i)) (g (suc i)) η (max₊ δ η)
          (Q.≤max' (fst δ) (fst η)) (tail i) }

match-rounded : ∀ {n} (xs ys : Vec (fst M) n) ε → Match xs ε ys →
  PT.∥ Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) × Match xs δ ys ∥₁
match-rounded {n} xs ys ε = PT.rec PT.isPropPropTrunc λ { (σ , close) →
  PT.map (λ { (δ , below , smaller) → δ , below , PT.∣ σ , smaller ∣₁ })
    (finite-rounded n (λ i → lookup i xs) (λ i → lookup (equivFun σ i) ys) ε close) }
