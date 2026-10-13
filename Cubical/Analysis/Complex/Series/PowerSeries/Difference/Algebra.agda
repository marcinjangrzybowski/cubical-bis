module Cubical.Analysis.Complex.Series.PowerSeries.Difference.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as Ring
open import Cubical.Tactics.CommRingSolver

-- The monomial divided difference is a finite polynomial, even on the
-- diagonal. Abstract ring proofs keep completion arithmetic out of solving.
module DifferenceAlgebra {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  private module T = Ring.RingTheory (CommRing→Ring R)
  private module P = Exponentiation R

  factor : fst R → fst R → ℕ → fst R
  factor x y zero = 1r
  factor x y (suc n) = (y P.^ suc n) + x · factor x y n

  opaque
    zeroEquation : ∀ x y → factor x y zero ≡ 1r
    zeroEquation x y = refl

    stepEquation : ∀ x y n → factor x y (suc n) ≡ (y P.^ suc n) + x · factor x y n
    stepEquation x y n = refl

  opaque
    private
      productDifference : ∀ x y p q →
        y · p - x · q ≡ (y - x) · p + x · (p - q)
      productDifference x y p q = solve! R

      interchange : ∀ a b c → a · (b · c) ≡ b · (a · c)
      interchange a b c = solve! R

      collect : ∀ x c p → x · p + x · (c · p) ≡ (c + 1r) · (x · p)
      collect x c p = solve! R

  opaque
    identity : ∀ x y n → (y P.^ suc n) - (x P.^ suc n) ≡ (y - x) · factor x y n
    identity x y zero = cong₂ _-_ (·IdR y) (·IdR x) ∙ sym (·IdR (y - x))
    identity x y (suc n) = productDifference x y (y P.^ suc n) (x P.^ suc n)
      ∙ cong (λ v → (y - x) · (y P.^ suc n) + x · v) (identity x y n)
      ∙ cong ((y - x) · (y P.^ suc n) +_) (interchange x (y - x) (factor x y n))
      ∙ sym (·DistR+ (y - x) (y P.^ suc n) (x · factor x y n))

    diagonal : (natural : ℕ → fst R) → natural (suc zero) ≡ 1r →
      (∀ n → natural (suc n) ≡ natural n + 1r) →
      ∀ x n → factor x x n ≡ natural (suc n) · (x P.^ n)
    diagonal natural one next x zero = sym one ∙ sym (·IdR (natural (suc zero)))
    diagonal natural one next x (suc n) =
      cong (λ v → (x P.^ suc n) + x · v) (diagonal natural one next x n)
      ∙ collect x (natural (suc n)) (x P.^ n)
      ∙ cong (_· (x P.^ suc n)) (sym (next (suc n)))

    coefficientIdentity : ∀ a x y n →
      a · (y P.^ suc n) - a · (x P.^ suc n) ≡ (y - x) · (a · factor x y n)
    coefficientIdentity a x y n = sym (T.·DistR- a (y P.^ suc n) (x P.^ suc n))
      ∙ cong (a ·_) (identity x y n) ∙ interchange a (y - x) (factor x y n)

    coefficientDiagonal : (natural : ℕ → fst R) → natural (suc zero) ≡ 1r →
      (∀ n → natural (suc n) ≡ natural n + 1r) → ∀ a x n →
      a · factor x x n ≡ (natural (suc n) · a) · (x P.^ n)
    coefficientDiagonal natural one next a x n =
      cong (a ·_) (diagonal natural one next x n)
      ∙ interchange a (natural (suc n)) (x P.^ n)
      ∙ ·Assoc (natural (suc n)) a (x P.^ n)

  -- Keep induction on powers abstract when its property contains completed
  -- real inequalities or continuity predicates.
  powerInduction : ∀ {ℓA ℓP} {A : Type ℓA}
    (property : (A → fst R) → Type ℓP) (coordinate : A → fst R) →
    property (λ _ → 1r) →
    (∀ n → property (λ x → coordinate x P.^ n) →
      property (λ x → coordinate x · (coordinate x P.^ n))) →
    ∀ n → property (λ x → coordinate x P.^ n)
  powerInduction property coordinate initial step zero = initial
  powerInduction property coordinate initial step (suc n) =
    step n (powerInduction property coordinate initial step n)
