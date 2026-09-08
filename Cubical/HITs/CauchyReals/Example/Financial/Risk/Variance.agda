module Cubical.HITs.CauchyReals.Example.Financial.Risk.Variance where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Probability public
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance
open import Cubical.Algebra.OrderedCommRing.Properties

private
  module RealOrder = OrderedCommRingTheory ℝOrderedCommRing

-- Dispersion is a second diagnostic alongside one-sided loss risk. Its
-- definition uses only finite expectations and multiplication, so no square
-- root or division by a possibly zero standard deviation is required.
square : ℝ → ℝ
square x = x ·ᵣ x

square-nonnegative : (x : ℝ) → 0 ≤ᵣ square x
square-nonnegative = RealOrder.0≤²

centered : ∀ {n} → Distribution n → Vector n → Vector n
centered P X i = X i -ᵣ expectation P X

variance : ∀ {n} → Distribution n → Vector n → ℝ
variance P X = expectation P (λ i → square (centered P X i))

covariance : ∀ {n} → Distribution n → Vector n → Vector n → ℝ
covariance P X Y = expectation P (λ i → centered P X i ·ᵣ centered P Y i)

private
  subtract-self : ∀ a → a -ᵣ a ≡ 0
  subtract-self a = ℝ!

  center-add-algebra : ∀ a b c d →
    (a +ᵣ b) -ᵣ (c +ᵣ d) ≡ (a -ᵣ c) +ᵣ (b -ᵣ d)
  center-add-algebra a b c d = ℝ!

  center-scale-algebra : ∀ a x m → a ·ᵣ x -ᵣ a ·ᵣ m ≡ a ·ᵣ (x -ᵣ m)
  center-scale-algebra a x m = ℝ!

  center-cash-algebra : ∀ x m c → (x +ᵣ c) -ᵣ (m +ᵣ c) ≡ x -ᵣ m
  center-cash-algebra x m c = ℝ!

  square-zero : square 0 ≡ 0
  square-zero = ℝ!

  square-add : ∀ a b →
    square (a +ᵣ b) ≡ (square a +ᵣ 2 ·ᵣ (a ·ᵣ b)) +ᵣ square b
  square-add a b = ℝ!

  square-scale : ∀ a b → square (a ·ᵣ b) ≡ square a ·ᵣ square b
  square-scale a b = ℝ!

centered-mean-zero : ∀ {n} (P : Distribution n) (X : Vector n) →
  expectation P (centered P X) ≡ 0
centered-mean-zero P X = expectation-cash P X (-ᵣ expectation P X)
  ∙ subtract-self (expectation P X)

centered-add : ∀ {n} (P : Distribution n) (X Y : Vector n) i →
  centered P (λ j → X j +ᵣ Y j) i ≡ centered P X i +ᵣ centered P Y i
centered-add P X Y i =
  cong (λ m → (X i +ᵣ Y i) -ᵣ m) (expectation-add P X Y)
  ∙ center-add-algebra (X i) (Y i) (expectation P X) (expectation P Y)

centered-scale : ∀ {n} (P : Distribution n) a (X : Vector n) i →
  centered P (λ j → a ·ᵣ X j) i ≡ a ·ᵣ centered P X i
centered-scale P a X i =
  cong (λ m → (a ·ᵣ X i) -ᵣ m) (expectation-scale P a X)
  ∙ center-scale-algebra a (X i) (expectation P X)

centered-cash : ∀ {n} (P : Distribution n) (X : Vector n) c i →
  centered P (λ j → X j +ᵣ c) i ≡ centered P X i
centered-cash P X c i =
  cong (λ m → (X i +ᵣ c) -ᵣ m) (expectation-cash P X c)
  ∙ center-cash-algebra (X i) (expectation P X) c

centered-constant : ∀ {n} (P : Distribution n) c i →
  centered P (λ _ → c) i ≡ 0
centered-constant P c i = cong (λ m → c -ᵣ m) (expectation-constant P c)
  ∙ subtract-self c

variance-nonnegative : ∀ {n} (P : Distribution n) (X : Vector n) →
  0 ≤ᵣ variance P X
variance-nonnegative P X = expectation-nonnegative P
  (λ i → square (centered P X i))
  (λ i → square-nonnegative (centered P X i))

variance-constant : ∀ {n} (P : Distribution n) c →
  variance P (λ _ → c) ≡ 0
variance-constant P c =
  cong (expectation P) (funExt (λ i →
    cong square (centered-constant P c i) ∙ square-zero))
  ∙ expectation-constant P 0

variance-cash : ∀ {n} (P : Distribution n) (X : Vector n) c →
  variance P (λ i → X i +ᵣ c) ≡ variance P X
variance-cash P X c = cong (expectation P)
  (funExt (λ i → cong square (centered-cash P X c i)))

variance-scale : ∀ {n} (P : Distribution n) a (X : Vector n) →
  variance P (λ i → a ·ᵣ X i) ≡ square a ·ᵣ variance P X
variance-scale P a X =
  cong (expectation P) (funExt (λ i →
    cong square (centered-scale P a X i)
    ∙ square-scale a (centered P X i)))
  ∙ expectation-scale P (square a) (λ i → square (centered P X i))

covariance-symmetric : ∀ {n} (P : Distribution n) (X Y : Vector n) →
  covariance P X Y ≡ covariance P Y X
covariance-symmetric P X Y = cong (expectation P)
  (funExt (λ i → ·ᵣComm (centered P X i) (centered P Y i)))

covariance-self : ∀ {n} (P : Distribution n) (X : Vector n) →
  covariance P X X ≡ variance P X
covariance-self P X = refl

-- Negative covariance can reduce dispersion. The cross term is retained
-- explicitly instead of assuming independent asset losses.
variance-add : ∀ {n} (P : Distribution n) (X Y : Vector n) →
  variance P (λ i → X i +ᵣ Y i)
  ≡ (variance P X +ᵣ 2 ·ᵣ covariance P X Y) +ᵣ variance P Y
variance-add P X Y =
  cong (expectation P) (funExt (λ i →
    cong square (centered-add P X Y i)
    ∙ square-add (centered P X i) (centered P Y i)))
  ∙ expectation-add P
      (λ i → square (centered P X i) +ᵣ
        2 ·ᵣ (centered P X i ·ᵣ centered P Y i))
      (λ i → square (centered P Y i))
  ∙ cong (_+ᵣ variance P Y)
      (expectation-add P (λ i → square (centered P X i))
        (λ i → 2 ·ᵣ (centered P X i ·ᵣ centered P Y i)))
  ∙ cong (λ c → (variance P X +ᵣ c) +ᵣ variance P Y)
      (expectation-scale P 2 (λ i → centered P X i ·ᵣ centered P Y i))

covariance-scale-left : ∀ {n} (P : Distribution n) a (X Y : Vector n) →
  covariance P (λ i → a ·ᵣ X i) Y ≡ a ·ᵣ covariance P X Y
covariance-scale-left P a X Y =
  cong (expectation P) (funExt (λ i →
    cong (_·ᵣ centered P Y i) (centered-scale P a X i)
    ∙ sym (·ᵣAssoc a (centered P X i) (centered P Y i))))
  ∙ expectation-scale P a (λ i → centered P X i ·ᵣ centered P Y i)

covariance-scale-right : ∀ {n} (P : Distribution n) a (X Y : Vector n) →
  covariance P X (λ i → a ·ᵣ Y i) ≡ a ·ᵣ covariance P X Y
covariance-scale-right P a X Y = covariance-symmetric P X (λ i → a ·ᵣ Y i)
  ∙ covariance-scale-left P a Y X
  ∙ cong (a ·ᵣ_) (covariance-symmetric P Y X)

-- The two-asset mean-variance portfolio formula holds for arbitrary real
-- holdings, including short positions, without nonnegativity assumptions.
variance-two-assets : ∀ {n} (P : Distribution n) a b (X Y : Vector n) →
  variance P (λ i → a ·ᵣ X i +ᵣ b ·ᵣ Y i)
  ≡ (square a ·ᵣ variance P X +ᵣ
      2 ·ᵣ (a ·ᵣ (b ·ᵣ covariance P X Y))) +ᵣ square b ·ᵣ variance P Y
variance-two-assets P a b X Y =
  variance-add P (λ i → a ·ᵣ X i) (λ i → b ·ᵣ Y i)
  ∙ cong₃ (λ v c w → (v +ᵣ 2 ·ᵣ c) +ᵣ w)
      (variance-scale P a X)
      (covariance-scale-left P a X (λ i → b ·ᵣ Y i)
        ∙ cong (a ·ᵣ_) (covariance-scale-right P b X Y))
      (variance-scale P b Y)
