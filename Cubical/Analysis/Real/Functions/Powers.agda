module Cubical.Analysis.Real.Functions.Powers where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base using (ℕ; zero; suc)
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws

open import Cubical.Relation.Premetric.Mappings


powℚ : ℚ → ℕ → ℚ
powℚ q zero = 1
powℚ q (suc n) = q ℚ.· powℚ q n

powℝ : ℝ → ℕ → ℝ
powℝ x zero = 1ℝ
powℝ x (suc n) = x · powℝ x n

pow-rat : ∀ q n → powℝ (rat q) n ≡ rat (powℚ q n)
pow-rat q zero = refl
pow-rat q (suc n) =
  cong (rat q ·_) (pow-rat q n)
  ∙ mul-rat q (powℚ q n)

private
  identity-isContinuous : isContinuous
    (ℝPremetricSpace .snd) (λ x → x) (ℝPremetricSpace .snd)
  identity-isContinuous = isNonExpanding→isContinuous
    (ℝPremetricSpace .snd) (λ x → x) (ℝPremetricSpace .snd)
    λ where
      .IsNonExpanding.pres≈ _ _ _ x∼y → x∼y

  constantOne-isContinuous : isContinuous
    (ℝPremetricSpace .snd) (λ _ → 1ℝ) (ℝPremetricSpace .snd)
  constantOne-isContinuous = isNonExpanding→isContinuous
    (ℝPremetricSpace .snd) (λ _ → 1ℝ) (ℝPremetricSpace .snd)
    λ where
      .IsNonExpanding.pres≈ _ _ ε _ → refl∼ 1ℝ ε


pow-isContinuous : ∀ n → isContinuous
  (ℝPremetricSpace .snd) (λ x → powℝ x n) (ℝPremetricSpace .snd)
pow-isContinuous zero = constantOne-isContinuous
pow-isContinuous (suc n) = mulOfContinuousIsContinuous
  (ℝPremetricSpace .snd)
  (λ x → x) (λ x → powℝ x n)
  identity-isContinuous (pow-isContinuous n)

squareℝ : ℝ → ℝ
squareℝ x = x · x

square-rat : ∀ q → squareℝ (rat q) ≡ rat (q ℚ.· q)
square-rat q = mul-rat q q

square-isContinuous : isContinuous
  (ℝPremetricSpace .snd) squareℝ (ℝPremetricSpace .snd)
square-isContinuous = mulOfContinuousIsContinuous
  (ℝPremetricSpace .snd)
  (λ x → x) (λ x → x)
  identity-isContinuous identity-isContinuous
