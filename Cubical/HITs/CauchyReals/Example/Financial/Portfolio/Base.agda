module Cubical.HITs.CauchyReals.Example.Financial.Portfolio.Base where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Probability public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Properties
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- A column contains losses per unit of one asset across the scenarios.
Market : ℕ → ℕ → Type₀
Market assets scenarios = Fin assets → Vector scenarios

portfolioLoss : ∀ {m n} → Market m n → Vector m → Vector n
portfolioLoss M holdings scenario = dot holdings (λ asset → M asset scenario)

portfolio-add : ∀ {m n} (M : Market m n) (u v : Vector m) i →
  portfolioLoss M (λ a → u a +ᵣ v a) i ≡ portfolioLoss M u i +ᵣ portfolioLoss M v i
portfolio-add M u v i = dot-left-add u v (λ a → M a i)

portfolio-scale : ∀ {m n} (M : Market m n) c (u : Vector m) i →
  portfolioLoss M (λ a → c ·ᵣ u a) i ≡ c ·ᵣ portfolioLoss M u i
portfolio-scale M c u i = dot-left-scale c u (λ a → M a i)

mix : ∀ {n} → ℝ → ℝ → Vector n → Vector n → Vector n
mix a b X Y i = a ·ᵣ X i +ᵣ b ·ᵣ Y i

portfolio-mix : ∀ {m n} (M : Market m n) a b (u v : Vector m) i →
  portfolioLoss M (mix a b u v) i ≡ mix a b (portfolioLoss M u) (portfolioLoss M v) i
portfolio-mix M a b u v i = portfolio-add M (λ j → a ·ᵣ u j) (λ j → b ·ᵣ v j) i
  ∙ cong₂ _+ᵣ_ (portfolio-scale M a u i) (portfolio-scale M b v i)

-- A fully invested long-only allocation has exactly the laws of a finite
-- distribution. This reuses both its set structure and proof-irrelevant laws.
Allocation : ℕ → Type₀
Allocation = Distribution

mix-allocation : ∀ {m} a b → 0 ≤ᵣ a → 0 ≤ᵣ b → a +ᵣ b ≡ 1 →
  Allocation m → Allocation m → Allocation m
mix-allocation a b a₊ b₊ total U V = mix a b (probability U) (probability V) ,
  (λ i → nonnegative-add _ _
    (nonnegative-mul a _ a₊ (probability-nonnegative U i))
    (nonnegative-mul b _ b₊ (probability-nonnegative V i))) ,
  (sum-add (λ i → a ·ᵣ probability U i) (λ i → b ·ᵣ probability V i)
    ∙ cong₂ _+ᵣ_ (sum-scale a (probability U)) (sum-scale b (probability V))
    ∙ cong₂ _+ᵣ_ (cong (a ·ᵣ_) (probability-total U) ∙ ·IdR a)
        (cong (b ·ᵣ_) (probability-total V) ∙ ·IdR b)
    ∙ total)

UnitWeight : Type₀
UnitWeight = Σ[ w ∈ ℝ ] ((0 ≤ᵣ w) × (w ≤ᵣ 1))

complement-nonnegative : (w : UnitWeight) → 0 ≤ᵣ 1 -ᵣ fst w
complement-nonnegative (w , lower , upper) = x≤y→0≤y-x w 1 upper

rebalance : ∀ {m} → UnitWeight → Allocation m → Allocation m → Allocation m
rebalance (w , lower , upper) =
  mix-allocation w (1 -ᵣ w) lower (x≤y→0≤y-x w 1 upper) total
  where
  total : w +ᵣ (1 -ᵣ w) ≡ 1
  total = ℝ!

-- Finite Fubini and linearity justify computing the portfolio mean from the
-- vector of individual asset means. Holdings need not be nonnegative here.
portfolio-expectation : ∀ {m n} (P : Distribution n) (M : Market m n) u →
  expectation P (portfolioLoss M u) ≡ dot u (λ a → expectation P (M a))
portfolio-expectation P M u =
  sum-cong _ _ (λ i → sym (sum-scale (probability P i) (λ a → u a ·ᵣ M a i)))
  ∙ sum-exchange (λ i a → probability P i ·ᵣ (u a ·ᵣ M a i))
  ∙ sum-cong _ _ (λ a →
      sum-cong _ _ (λ i → commute (probability P i) (u a) (M a i))
      ∙ sum-scale (u a) (λ i → probability P i ·ᵣ M a i))
  where
  commute : ∀ p u x → p ·ᵣ (u ·ᵣ x) ≡ u ·ᵣ (p ·ᵣ x)
  commute p u x = ℝ!

-- Asset-specific error bounds aggregate into a holdings-weighted reserve.
-- The result is valid for long-only holdings of any total notional.
portfolio-model-error : ∀ {m n} (M N : Market m n) u error →
  (∀ a → 0 ≤ᵣ u a) → (∀ a i → M a i ≤ᵣ N a i +ᵣ error a) →
  ∀ i → portfolioLoss M u i ≤ᵣ portfolioLoss N u i +ᵣ dot u error
portfolio-model-error M N u error u₊ bound i =
  isTrans≤≡ᵣ _ _ _
    (dot-monotone u (λ a → M a i) (λ a → N a i +ᵣ error a) u₊ (λ a → bound a i))
    (dot-add u (λ a → N a i) error)

-- Stress certificates are scenario checks, not Boolean tests of real order.
StressCertificate : ∀ {m n} → Market m (suc n) → Vector m → ℝ → Type₀
StressCertificate M u budget = ∀ i → portfolioLoss M u i ≤ᵣ budget

stress-sound : ∀ {m n} (M : Market m (suc n)) u budget →
  StressCertificate M u budget → worstCase (portfolioLoss M u) ≤ᵣ budget
stress-sound M u budget = worstCase-least (portfolioLoss M u) budget

stress-complete : ∀ {m n} (M : Market m (suc n)) u budget →
  worstCase (portfolioLoss M u) ≤ᵣ budget → StressCertificate M u budget
stress-complete M u budget bound i =
  isTrans≤ᵣ _ _ _ (worstCase-upper (portfolioLoss M u) i) bound

stress-mix : ∀ {m n} (M : Market m (suc n)) a b u v s t →
  0 ≤ᵣ a → 0 ≤ᵣ b → StressCertificate M u s → StressCertificate M v t →
  StressCertificate M (mix a b u v) (a ·ᵣ s +ᵣ b ·ᵣ t)
stress-mix M a b u v s t a₊ b₊ cu cv i =
  isTrans≡≤ᵣ _ _ _ (portfolio-mix M a b u v i)
    (≤ᵣMonotone+ᵣ _ _ _ _
      (≤ᵣ-o·ᵣ _ _ a a₊ (cu i)) (≤ᵣ-o·ᵣ _ _ b b₊ (cv i)))
