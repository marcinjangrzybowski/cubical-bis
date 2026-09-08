module Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base using (NonExpanding₂)
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring using (module Rℝ)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Lattice
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- The lattice operation is defined on the Cauchy-real HIT.  Taking a
-- positive part consequently requires no decidable comparison of reals.
positivePart : ℝ → ℝ
positivePart x = maxᵣ x 0

positivePart-nonnegative : ∀ x → 0 ≤ᵣ positivePart x
positivePart-nonnegative x =
  isTrans≤≡ᵣ _ _ _ (≤maxᵣ 0 x) (maxᵣComm 0 x)

≤positivePart : ∀ x → x ≤ᵣ positivePart x
≤positivePart x = ≤maxᵣ x 0

positivePart-upper : ∀ x u → x ≤ᵣ u → 0 ≤ᵣ u → positivePart x ≤ᵣ u
positivePart-upper x u = max≤-lem x 0 u

positivePart-monotone : ∀ x y → x ≤ᵣ y → positivePart x ≤ᵣ positivePart y
positivePart-monotone x y x≤y =
  maxMonotoneᵣ x y 0 0 x≤y (≤ᵣ-refl 0)

positivePart-of-nonnegative : ∀ x → 0 ≤ᵣ x → positivePart x ≡ x
positivePart-of-nonnegative x 0≤x = maxᵣComm x 0 ∙ ≤ᵣ→≡ 0≤x

positivePart-of-nonpositive : ∀ x → x ≤ᵣ 0 → positivePart x ≡ 0
positivePart-of-nonpositive x x≤0 = ≤ᵣ→≡ x≤0

positivePart-zero : positivePart 0 ≡ 0
positivePart-zero = maxᵣIdem 0

positivePart-rat : ∀ q → positivePart (rat q) ≡ rat (ℚ.max q 0)
positivePart-rat q = maxᵣ-rat q 0

-- The higher-inductive lifting of max preserves closeness.  In particular,
-- certified Cauchy approximations remain certified after taking a shortfall.
opaque
  unfolding maxᵣ

  positivePart-nonexpanding : ∀ x y ε → x ∼[ ε ] y →
    positivePart x ∼[ ε ] positivePart y
  positivePart-nonexpanding x y ε = NonExpanding₂.go∼L maxR 0 x y ε

private
  nonnegative-sum : ∀ x y → 0 ≤ᵣ x → 0 ≤ᵣ y → 0 ≤ᵣ x +ᵣ y
  nonnegative-sum x y 0≤x 0≤y =
    subst (_≤ᵣ (x +ᵣ y)) (+IdL 0)
      (≤ᵣMonotone+ᵣ 0 x 0 y 0≤x 0≤y)

  nonnegative-product : ∀ a x → 0 ≤ᵣ a → 0 ≤ᵣ x → 0 ≤ᵣ a ·ᵣ x
  nonnegative-product a x 0≤a 0≤x =
    subst (_≤ᵣ (a ·ᵣ x)) (Rℝ.0RightAnnihilates a)
      (≤ᵣ-o·ᵣ 0 x a 0≤a 0≤x)

  cancel-threshold : ∀ x t → t +ᵣ (x -ᵣ t) ≡ x
  cancel-threshold x t =
    +ᵣComm t (x -ᵣ t)
    ∙ sym (+ᵣAssoc x (-ᵣ t) t)
    ∙ cong (x +ᵣ_) (+ᵣComm (-ᵣ t) t ∙ +-ᵣ t)
    ∙ +IdR x

  difference-of-sums : ∀ x y s t →
    (x +ᵣ y) -ᵣ (s +ᵣ t) ≡ (x -ᵣ s) +ᵣ (y -ᵣ t)
  difference-of-sums x y s t =
    cong ((x +ᵣ y) +ᵣ_) (sym (Rℝ.-Dist s t))
    ∙ Rℝ.+ShufflePairs x y (-ᵣ s) (-ᵣ t)

positivePart-subadditive : ∀ x y →
  positivePart (x +ᵣ y) ≤ᵣ positivePart x +ᵣ positivePart y
positivePart-subadditive x y = positivePart-upper _ _
  (≤ᵣMonotone+ᵣ _ _ _ _ (≤positivePart x) (≤positivePart y))
  (nonnegative-sum _ _
    (positivePart-nonnegative x) (positivePart-nonnegative y))

-- This inequality, valid also when a = 0, is enough for all of the
-- diversification estimates below; it never requires division by a.
positivePart-scale-bound : ∀ a x → 0 ≤ᵣ a →
  positivePart (a ·ᵣ x) ≤ᵣ a ·ᵣ positivePart x
positivePart-scale-bound a x 0≤a = positivePart-upper _ _
  (≤ᵣ-o·ᵣ _ _ a 0≤a (≤positivePart x))
  (nonnegative-product a _ 0≤a (positivePart-nonnegative x))

-- In particular this is convexity when a + b = 1.  Keeping the stronger
-- conic statement makes it useful for portfolios with arbitrary notionals.
positivePart-weighted-bound : ∀ a b x y → 0 ≤ᵣ a → 0 ≤ᵣ b →
  positivePart (a ·ᵣ x +ᵣ b ·ᵣ y)
    ≤ᵣ a ·ᵣ positivePart x +ᵣ b ·ᵣ positivePart y
positivePart-weighted-bound a b x y 0≤a 0≤b =
  isTrans≤ᵣ _ _ _ (positivePart-subadditive _ _)
    (≤ᵣMonotone+ᵣ _ _ _ _
      (positivePart-scale-bound a x 0≤a)
      (positivePart-scale-bound b y 0≤b))

-- A one-sided perturbation estimate is enough to transport upper bounds
-- from an approximate loss model to the actual loss model.
positivePart-perturbation : ∀ x y ε → 0 ≤ᵣ ε → x ≤ᵣ y +ᵣ ε →
  positivePart x ≤ᵣ positivePart y +ᵣ ε
positivePart-perturbation x y ε 0≤ε x≤y+ε =
  positivePart-upper _ _
    (isTrans≤ᵣ _ _ _ x≤y+ε (≤ᵣ-+o _ _ ε (≤positivePart y)))
    (nonnegative-sum _ _ (positivePart-nonnegative y) 0≤ε)

-- stopLoss x t is the excess of the loss x over a chosen threshold t.
stopLoss : ℝ → ℝ → ℝ
stopLoss x t = positivePart (x -ᵣ t)

stopLoss-nonnegative : ∀ x t → 0 ≤ᵣ stopLoss x t
stopLoss-nonnegative x t = positivePart-nonnegative (x -ᵣ t)

stopLoss-rat : ∀ x t →
  stopLoss (rat x) (rat t) ≡ rat (ℚ.max (x ℚ.- t) 0)
stopLoss-rat x t =
  cong positivePart (-ᵣ-rat₂ x t) ∙ positivePart-rat (x ℚ.- t)

stopLoss-nonexpanding : ∀ x y t ε → x ∼[ ε ] y →
  stopLoss x t ∼[ ε ] stopLoss y t
stopLoss-nonexpanding x y t ε x∼y =
  positivePart-nonexpanding _ _ ε (+ᵣ-∼ x y (-ᵣ t) ε x∼y)

stopLoss-monotone : ∀ x y t → x ≤ᵣ y → stopLoss x t ≤ᵣ stopLoss y t
stopLoss-monotone x y t x≤y =
  positivePart-monotone _ _ (≤ᵣ-+o x y (-ᵣ t) x≤y)

stopLoss-antitone-threshold : ∀ x s t → s ≤ᵣ t →
  stopLoss x t ≤ᵣ stopLoss x s
stopLoss-antitone-threshold x s t s≤t =
  positivePart-monotone _ _ (≤ᵣ-o+ _ _ x (-ᵣ≤ᵣ s t s≤t))

stopLoss-perturbation : ∀ x y t ε → 0 ≤ᵣ ε → x ≤ᵣ y +ᵣ ε →
  stopLoss x t ≤ᵣ stopLoss y t +ᵣ ε
stopLoss-perturbation x y t ε 0≤ε x≤y+ε =
  positivePart-perturbation _ _ ε 0≤ε
    (isTrans≤≡ᵣ _ _ _ (≤ᵣ-+o _ _ (-ᵣ t) x≤y+ε)
      (sym (+ᵣAssoc y ε (-ᵣ t))
      ∙ cong (y +ᵣ_) (+ᵣComm ε (-ᵣ t))
      ∙ +ᵣAssoc y (-ᵣ t) ε))

stopLoss-reconstruct : ∀ x t → x ≤ᵣ t +ᵣ stopLoss x t
stopLoss-reconstruct x t =
  subst (_≤ᵣ (t +ᵣ stopLoss x t)) (cancel-threshold x t)
    (≤ᵣ-o+ _ _ t (≤positivePart (x -ᵣ t)))

stopLoss-zero-below : ∀ x t → x ≤ᵣ t → stopLoss x t ≡ 0
stopLoss-zero-below x t x≤t = positivePart-of-nonpositive _
  (subst ((x -ᵣ t) ≤ᵣ_) (+-ᵣ t) (≤ᵣ-+o x t (-ᵣ t) x≤t))

-- A nonnegative budget bounds a shortfall precisely when it covers the
-- original claim together with the threshold already available.
stopLoss-upper : ∀ x c b → 0 ≤ᵣ b →
  x ≤ᵣ c +ᵣ b → stopLoss x c ≤ᵣ b
stopLoss-upper x c b b₊ coverage = positivePart-upper (x -ᵣ c) b
  (isTrans≤≡ᵣ _ _ _ (≤ᵣ-+o x (c +ᵣ b) (-ᵣ c) coverage) cancel) b₊
  where
  cancel : (c +ᵣ b) -ᵣ c ≡ b
  cancel = ℝ!

stopLoss-evaluate : ∀ x c r → x -ᵣ c ≡ r →
  0 ≤ᵣ r → stopLoss x c ≡ r
stopLoss-evaluate x c r equation r₊ =
  cong positivePart equation ∙ positivePart-of-nonnegative r r₊

stopLoss-at-zero : ∀ x → 0 ≤ᵣ x → stopLoss x 0 ≡ x
stopLoss-at-zero x = stopLoss-evaluate x 0 x difference
  where
  difference : x -ᵣ 0 ≡ x
  difference = ℝ!

stopLoss-translation : ∀ x t c → stopLoss (c +ᵣ x) (c +ᵣ t) ≡ stopLoss x t
stopLoss-translation x t c =
  cong positivePart (sym (Rℝ.translatedDifference c x t))

stopLoss-subadditive : ∀ x y s t →
  stopLoss (x +ᵣ y) (s +ᵣ t) ≤ᵣ stopLoss x s +ᵣ stopLoss y t
stopLoss-subadditive x y s t =
  isTrans≡≤ᵣ _ _ _ (cong positivePart (difference-of-sums x y s t))
    (positivePart-subadditive (x -ᵣ s) (y -ᵣ t))

stopLoss-scale-bound : ∀ a x t → 0 ≤ᵣ a →
  stopLoss (a ·ᵣ x) (a ·ᵣ t) ≤ᵣ a ·ᵣ stopLoss x t
stopLoss-scale-bound a x t 0≤a =
  isTrans≡≤ᵣ _ _ _ (cong positivePart (sym (·DistL- a x t)))
    (positivePart-scale-bound a (x -ᵣ t) 0≤a)

stopLoss-weighted-bound : ∀ a b x y s t → 0 ≤ᵣ a → 0 ≤ᵣ b →
  stopLoss (a ·ᵣ x +ᵣ b ·ᵣ y) (a ·ᵣ s +ᵣ b ·ᵣ t)
    ≤ᵣ a ·ᵣ stopLoss x s +ᵣ b ·ᵣ stopLoss y t
stopLoss-weighted-bound a b x y s t 0≤a 0≤b =
  isTrans≤ᵣ _ _ _ (stopLoss-subadditive _ _ _ _)
    (≤ᵣMonotone+ᵣ _ _ _ _
      (stopLoss-scale-bound a x s 0≤a)
      (stopLoss-scale-bound b y t 0≤b))
