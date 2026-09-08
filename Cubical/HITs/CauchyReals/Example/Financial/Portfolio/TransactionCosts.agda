module Cubical.HITs.CauchyReals.Example.Financial.Portfolio.TransactionCosts where

open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.Base public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.RiskLaws
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.HITs.PropositionalTruncation as PT

-- Linear execution fees: a rate is charged on the absolute traded amount.
-- Holdings may be signed; order results require nonnegative fee rates.
-- Fees are an additional loss in the same units and horizon as market loss.
transactionCost : ∀ {m} → Vector m → Vector m → Vector m → ℝ
transactionCost rates old target = dot rates (λ i → absᵣ (target i -ᵣ old i))

transactionCost-nonnegative : ∀ {m} (rates old target : Vector m) →
  (∀ i → 0 ≤ᵣ rates i) → 0 ≤ᵣ transactionCost rates old target
transactionCost-nonnegative rates old target rates₊ =
  dot-nonnegative rates (λ i → absᵣ (target i -ᵣ old i)) rates₊
    (λ i → 0≤absᵣ (target i -ᵣ old i))

transactionCost-self : ∀ {m} (rates old : Vector m) → transactionCost rates old old ≡ 0
transactionCost-self {m} rates old =
  sum-cong _ (λ _ → 0)
    (λ i → cong (rates i ·ᵣ_) (cong absᵣ (+-ᵣ (old i)) ∙ absᵣ0)
      ∙ Rℝ.0RightAnnihilates (rates i))
  ∙ sum-zero m

private
  abs-difference-symmetric : ∀ x y → absᵣ (x -ᵣ y) ≡ absᵣ (y -ᵣ x)
  abs-difference-symmetric x y = cong absᵣ difference ∙ sym (-absᵣ (y -ᵣ x))
    where
    difference : x -ᵣ y ≡ -ᵣ (y -ᵣ x)
    difference = ℝ!

  abs-route-bound : ∀ old middle target →
    absᵣ (target -ᵣ old) ≤ᵣ absᵣ (middle -ᵣ old) +ᵣ absᵣ (target -ᵣ middle)
  abs-route-bound old middle target =
    isTrans≡≤ᵣ _ _ _ (cong absᵣ route) (absᵣ-triangle _ _)
    where
    route : target -ᵣ old ≡ (middle -ᵣ old) +ᵣ (target -ᵣ middle)
    route = ℝ!

  abs-nonnegative-scale : ∀ a x → 0 ≤ᵣ a → absᵣ (a ·ᵣ x) ≡ a ·ᵣ absᵣ x
  abs-nonnegative-scale a x a₊ =
    ·absᵣ a x ∙ cong (_·ᵣ absᵣ x) (absᵣNonNeg a a₊)

transactionCost-symmetric : ∀ {m} (rates old target : Vector m) →
  transactionCost rates old target ≡ transactionCost rates target old
transactionCost-symmetric rates old target =
  sum-cong _ _ (λ i → cong (rates i ·ᵣ_) (abs-difference-symmetric (target i) (old i)))

-- Under this proportional fee model, splitting a trade cannot cost less
-- than executing the direct net change. There are no fixed ticket charges.
transactionCost-triangle : ∀ {m} (rates old middle target : Vector m) →
  (∀ i → 0 ≤ᵣ rates i) → transactionCost rates old target
    ≤ᵣ transactionCost rates old middle +ᵣ transactionCost rates middle target
transactionCost-triangle rates old middle target rates₊ =
  isTrans≤≡ᵣ _ _ _
    (dot-monotone rates (λ i → absᵣ (target i -ᵣ old i))
      (λ i → absᵣ (middle i -ᵣ old i) +ᵣ absᵣ (target i -ᵣ middle i))
      rates₊ (λ i → abs-route-bound (old i) (middle i) (target i)))
    (dot-add rates (λ i → absᵣ (middle i -ᵣ old i))
      (λ i → absᵣ (target i -ᵣ middle i)))

transactionCost-rate-monotone : ∀ {m} (rates rates' old target : Vector m) →
  (∀ i → rates i ≤ᵣ rates' i) →
  transactionCost rates old target ≤ᵣ transactionCost rates' old target
transactionCost-rate-monotone rates rates' old target bound =
  sum-monotone _ _ (λ i → ≤ᵣ-·ᵣo (rates i) (rates' i) _
    (0≤absᵣ (target i -ᵣ old i)) (bound i))

transactionCost-scale-rates : ∀ {m} a (rates old target : Vector m) →
  transactionCost (λ i → a ·ᵣ rates i) old target ≡ a ·ᵣ transactionCost rates old target
transactionCost-scale-rates a rates old target =
  dot-left-scale a rates (λ i → absᵣ (target i -ᵣ old i))

-- A convex combination of target holdings gives a convex fee bound from
-- the SAME starting holdings. The rates and starting position are fixed.
transactionCost-convex : ∀ {m} (rates old u v : Vector m) a b →
  (∀ i → 0 ≤ᵣ rates i) → 0 ≤ᵣ a → 0 ≤ᵣ b → a +ᵣ b ≡ 1 →
  transactionCost rates old (mix a b u v)
    ≤ᵣ a ·ᵣ transactionCost rates old u +ᵣ b ·ᵣ transactionCost rates old v
transactionCost-convex rates old u v a b rates₊ a₊ b₊ total =
  isTrans≤≡ᵣ _ _ _
    (dot-monotone rates (λ i → absᵣ (mix a b u v i -ᵣ old i))
      (λ i → a ·ᵣ absᵣ (u i -ᵣ old i) +ᵣ b ·ᵣ absᵣ (v i -ᵣ old i))
      rates₊ pointwise)
    (dot-add rates (λ i → a ·ᵣ absᵣ (u i -ᵣ old i))
      (λ i → b ·ᵣ absᵣ (v i -ᵣ old i))
    ∙ cong₂ _+ᵣ_ (dot-scale rates a (λ i → absᵣ (u i -ᵣ old i)))
        (dot-scale rates b (λ i → absᵣ (v i -ᵣ old i))))
  where
  difference : ∀ x y z → a ·ᵣ x +ᵣ b ·ᵣ y -ᵣ z
    ≡ a ·ᵣ (x -ᵣ z) +ᵣ b ·ᵣ (y -ᵣ z)
  difference x y z =
    cong (λ value → (a ·ᵣ x +ᵣ b ·ᵣ y) -ᵣ value)
      (sym (cong (_·ᵣ z) total ∙ ·IdLᵣ z))
    ∙ ℝ!

  pointwise : ∀ i → absᵣ (mix a b u v i -ᵣ old i)
    ≤ᵣ a ·ᵣ absᵣ (u i -ᵣ old i) +ᵣ b ·ᵣ absᵣ (v i -ᵣ old i)
  pointwise i = isTrans≡≤ᵣ _ _ _ (cong absᵣ (difference (u i) (v i) (old i)))
    (isTrans≤≡ᵣ _ _ _ (absᵣ-triangle _ _)
      (cong₂ _+ᵣ_ (abs-nonnegative-scale a (u i -ᵣ old i) a₊)
        (abs-nonnegative-scale b (v i -ᵣ old i) b₊)))

-- Execution costs are deterministic scenario losses. This definition does
-- not model a funding account or deduct fees from the target notionals.
allInLoss : ∀ {m n} → Market m n → Vector m → Vector m → Vector m → Vector n
allInLoss M rates old target i = transactionCost rates old target +ᵣ portfolioLoss M target i

allIn-no-trade : ∀ {m n} (M : Market m n) rates old →
  allInLoss M rates old old ≡ portfolioLoss M old
allIn-no-trade M rates old = funExt λ i →
  cong (_+ᵣ portfolioLoss M old i) (transactionCost-self rates old)
  ∙ +IdL (portfolioLoss M old i)

allIn-convex : ∀ {m n} (M : Market m n) rates old u v a b →
  (∀ i → 0 ≤ᵣ rates i) → 0 ≤ᵣ a → 0 ≤ᵣ b → a +ᵣ b ≡ 1 →
  ∀ i → allInLoss M rates old (mix a b u v) i
    ≤ᵣ a ·ᵣ allInLoss M rates old u i +ᵣ b ·ᵣ allInLoss M rates old v i
allIn-convex M rates old u v a b rates₊ a₊ b₊ total i =
  isTrans≤≡ᵣ _ _ _
    (≤ᵣMonotone+ᵣ _ _ _ _
      (transactionCost-convex rates old u v a b rates₊ a₊ b₊ total)
      (≡ᵣWeaken≤ᵣ _ _ (portfolio-mix M a b u v i)))
    (distribute (transactionCost rates old u) (transactionCost rates old v)
      (portfolioLoss M u i) (portfolioLoss M v i))
  where
  distribute : ∀ cu cv xu xv →
    (a ·ᵣ cu +ᵣ b ·ᵣ cv) +ᵣ (a ·ᵣ xu +ᵣ b ·ᵣ xv)
      ≡ a ·ᵣ (cu +ᵣ xu) +ᵣ b ·ᵣ (cv +ᵣ xv)
  distribute cu cv xu xv = ℝ!

cash-expectation : ∀ {n} (P : Distribution n) (X : Vector n) c →
  expectation P (λ i → c +ᵣ X i) ≡ c +ᵣ expectation P X
cash-expectation P X c = expectation-add P (λ _ → c) X
  ∙ cong (_+ᵣ expectation P X) (expectation-constant P c)

allIn-expectation : ∀ {m n} (P : Distribution n) (M : Market m n) rates old target →
  expectation P (allInLoss M rates old target)
    ≡ transactionCost rates old target +ᵣ expectation P (portfolioLoss M target)
allIn-expectation P M rates old target =
  cash-expectation P (portfolioLoss M target) (transactionCost rates old target)

cash-worstCase : ∀ {n} (X : Vector (suc n)) c →
  worstCase (λ i → c +ᵣ X i) ≡ c +ᵣ worstCase X
cash-worstCase X c = cong worstCase (funExt (λ i → +ᵣComm c (X i)))
  ∙ worstCase-cash X c ∙ +ᵣComm (worstCase X) c

allIn-worstCase : ∀ {m n} (M : Market m (suc n)) rates old target →
  worstCase (allInLoss M rates old target)
    ≡ transactionCost rates old target +ᵣ worstCase (portfolioLoss M target)
allIn-worstCase M rates old target =
  cash-worstCase (portfolioLoss M target) (transactionCost rates old target)

module TailCosts {n : ℕ} (P : Distribution n) (level : TailLevel) where
  open TailRisk P level
  module Laws = CVaRLaws P level

  -- Useful when comparing costly portfolios at arbitrary trial thresholds.
  objective-cash-at : ∀ (X : Vector n) c t →
    objective (λ i → c +ᵣ X i) t ≡ c +ᵣ objective X (t -ᵣ c)
  objective-cash-at X c t =
    cong (objective (λ i → c +ᵣ X i)) (sym cancel)
    ∙ objective-cash X (t -ᵣ c) c
    where
    cancel : c +ᵣ (t -ᵣ c) ≡ t
    cancel = ℝ!

  accepted-cash : ∀ X c budget → Accepted X budget →
    Accepted (λ i → c +ᵣ X i) (c +ᵣ budget)
  accepted-cash X c budget = PT.map
    (λ (t , bound) → (c +ᵣ t) ,
      isTrans≡≤ᵣ _ _ _ (objective-cash X t c) (≤ᵣ-o+ _ _ c bound))

  certificate-cash : ∀ X c → OptimalityCertificate X →
    OptimalityCertificate (λ i → c +ᵣ X i)
  certificate-cash X c cert .threshold = c +ᵣ threshold cert
  certificate-cash X c cert .dual = dual cert
  certificate-cash X c cert .dual-admissible = dual-admissible cert
  certificate-cash X c cert .tight =
    objective-cash X (threshold cert) c ∙ cong (c +ᵣ_) (tight cert)
    ∙ sym (cash-expectation (dual cert) X c)

  allIn-objective : ∀ {m} (M : Market m n) rates old target t →
    objective (allInLoss M rates old target) t
      ≡ transactionCost rates old target
        +ᵣ objective (portfolioLoss M target) (t -ᵣ transactionCost rates old target)
  allIn-objective M rates old target =
    objective-cash-at (portfolioLoss M target) (transactionCost rates old target)

  allIn-CVaR : ∀ {m} (M : Market m n) rates old target r →
    IsCVaR (portfolioLoss M target) r →
    IsCVaR (allInLoss M rates old target) (transactionCost rates old target +ᵣ r)
  allIn-CVaR M rates old target r =
    Laws.IsCVaR-cash (portfolioLoss M target) r (transactionCost rates old target)

  allIn-accepted : ∀ {m} (M : Market m n) rates old target budget →
    Accepted (portfolioLoss M target) budget →
    Accepted (allInLoss M rates old target) (transactionCost rates old target +ᵣ budget)
  allIn-accepted M rates old target =
    accepted-cash (portfolioLoss M target) (transactionCost rates old target)

  allIn-certificate : ∀ {m} (M : Market m n) rates old target →
    OptimalityCertificate (portfolioLoss M target) →
    OptimalityCertificate (allInLoss M rates old target)
  allIn-certificate M rates old target =
    certificate-cash (portfolioLoss M target) (transactionCost rates old target)

  allIn-accepted-convex : ∀ {m} (M : Market m n) rates old u v a b budgetU budgetV →
    (∀ i → 0 ≤ᵣ rates i) → 0 ≤ᵣ a → 0 ≤ᵣ b → a +ᵣ b ≡ 1 →
    Accepted (allInLoss M rates old u) budgetU →
    Accepted (allInLoss M rates old v) budgetV →
    Accepted (allInLoss M rates old (mix a b u v)) (a ·ᵣ budgetU +ᵣ b ·ᵣ budgetV)
  allIn-accepted-convex M rates old u v a b budgetU budgetV rates₊ a₊ b₊ total pu pv =
    accepted-monotone (allInLoss M rates old (mix a b u v))
      (mix a b (allInLoss M rates old u) (allInLoss M rates old v))
      (a ·ᵣ budgetU +ᵣ b ·ᵣ budgetV)
      (allIn-convex M rates old u v a b rates₊ a₊ b₊ total)
      (accepted-weighted (allInLoss M rates old u) (allInLoss M rates old v)
        a b budgetU budgetV a₊ b₊ pu pv)
