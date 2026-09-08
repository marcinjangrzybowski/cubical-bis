module Cubical.HITs.CauchyReals.Example.Financial.Core.Finite where

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.HLevels public
open import Cubical.Data.Nat using (ℕ; zero; suc) public
open import Cubical.Data.Nat.Literals public
open import Cubical.Data.FinData.Base using (Fin) public
import Cubical.Data.FinData.Base as F

open import Cubical.HITs.CauchyReals.Foundation.Base public
open import Cubical.HITs.CauchyReals.Foundation.Closeness using (isSetℝ) public
open import Cubical.HITs.CauchyReals.Foundation.Order.Base public
open import Cubical.HITs.CauchyReals.Algebra.Multiplication public
open import Cubical.HITs.CauchyReals.Algebra.Ring public
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base public
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication public
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- Coordinates are data-finite, so all folds compute without choosing an
-- enumeration of an abstract finite type or deciding the order of reals.
Vector : ℕ → Type₀
Vector n = Fin n → ℝ

sum : ∀ {n} → Vector n → ℝ
sum {zero} x = 0
sum {suc n} x = x F.zero +ᵣ sum (λ i → x (F.suc i))

sum-cong : ∀ {n} (x y : Vector n) → (∀ i → x i ≡ y i) → sum x ≡ sum y
sum-cong x y p = cong sum (funExt p)

sum-zero : ∀ n → sum {n} (λ _ → 0) ≡ 0
sum-zero zero = refl
sum-zero (suc n) = cong (0 +ᵣ_) (sum-zero n) ∙ +IdL 0

private
  shuffle : ∀ a b c d → (a +ᵣ b) +ᵣ (c +ᵣ d) ≡ (a +ᵣ c) +ᵣ (b +ᵣ d)
  shuffle a b c d = ℝ!

sum-add : ∀ {n} (x y : Vector n) →
  sum (λ i → x i +ᵣ y i) ≡ sum x +ᵣ sum y
sum-add {zero} x y = sym (+IdL 0)
sum-add {suc n} x y =
  cong ((x F.zero +ᵣ y F.zero) +ᵣ_)
    (sum-add (λ i → x (F.suc i)) (λ i → y (F.suc i)))
  ∙ shuffle _ _ _ _

sum-scale : ∀ {n} a (x : Vector n) →
  sum (λ i → a ·ᵣ x i) ≡ a ·ᵣ sum x
sum-scale {zero} a x = ℝ!
sum-scale {suc n} a x =
  cong ((a ·ᵣ x F.zero) +ᵣ_) (sum-scale a (λ i → x (F.suc i)))
  ∙ sym (·DistL+ a _ _)

sum-negate : ∀ {n} (X : Vector n) → sum (λ i → -ᵣ X i) ≡ -ᵣ sum X
sum-negate {zero} X = ℝ!
sum-negate {suc n} X =
  cong ((-ᵣ X F.zero) +ᵣ_) (sum-negate (λ i → X (F.suc i))) ∙ collect _ _
  where
  collect : ∀ a b → (-ᵣ a) +ᵣ (-ᵣ b) ≡ -ᵣ (a +ᵣ b)
  collect a b = ℝ!


sum-monotone : ∀ {n} (x y : Vector n) →
  (∀ i → x i ≤ᵣ y i) → sum x ≤ᵣ sum y
sum-monotone {zero} x y p = ≤ᵣ-refl 0
sum-monotone {suc n} x y p =
  ≤ᵣMonotone+ᵣ _ _ _ _ (p F.zero)
    (sum-monotone (λ i → x (F.suc i)) (λ i → y (F.suc i))
      (λ i → p (F.suc i)))

sum-nonnegative : ∀ {n} (x : Vector n) → (∀ i → 0 ≤ᵣ x i) → 0 ≤ᵣ sum x
sum-nonnegative {n} x p =
  isTrans≡≤ᵣ _ _ _ (sym (sum-zero n)) (sum-monotone (λ _ → 0) x p)

nonnegative-add : ∀ x y → 0 ≤ᵣ x → 0 ≤ᵣ y → 0 ≤ᵣ x +ᵣ y
nonnegative-add x y p q =
  isTrans≡≤ᵣ _ _ _ (sym (+IdL 0)) (≤ᵣMonotone+ᵣ _ _ _ _ p q)

nonnegative-mul : ∀ x y → 0 ≤ᵣ x → 0 ≤ᵣ y → 0 ≤ᵣ x ·ᵣ y
nonnegative-mul x y p q =
  isTrans≡≤ᵣ _ _ _ (sym (Rℝ.0RightAnnihilates x)) (≤ᵣ-o·ᵣ 0 y x p q)

dot : ∀ {n} → Vector n → Vector n → ℝ
dot p x = sum (λ i → p i ·ᵣ x i)

dot-add : ∀ {n} (p x y : Vector n) →
  dot p (λ i → x i +ᵣ y i) ≡ dot p x +ᵣ dot p y
dot-add p x y =
  sum-cong _ _ (λ i → ·DistL+ (p i) (x i) (y i))
  ∙ sum-add (λ i → p i ·ᵣ x i) (λ i → p i ·ᵣ y i)

dot-scale : ∀ {n} (p : Vector n) a (x : Vector n) →
  dot p (λ i → a ·ᵣ x i) ≡ a ·ᵣ dot p x
dot-scale p a x = sum-cong _ _ (λ i → swap (p i) a (x i))
  ∙ sum-scale a (λ i → p i ·ᵣ x i)
  where
  swap : ∀ u v w → u ·ᵣ (v ·ᵣ w) ≡ v ·ᵣ (u ·ᵣ w)
  swap u v w = ℝ!

dot-constant : ∀ {n} (p : Vector n) c → dot p (λ _ → c) ≡ c ·ᵣ sum p
dot-constant p c = sum-cong _ _ (λ i → ·ᵣComm (p i) c) ∙ sum-scale c p

dot-monotone : ∀ {n} (p x y : Vector n) →
  (∀ i → 0 ≤ᵣ p i) → (∀ i → x i ≤ᵣ y i) → dot p x ≤ᵣ dot p y
dot-monotone p x y p₊ x≤y =
  sum-monotone _ _ (λ i → ≤ᵣ-o·ᵣ _ _ (p i) (p₊ i) (x≤y i))

dot-nonnegative : ∀ {n} (p x : Vector n) →
  (∀ i → 0 ≤ᵣ p i) → (∀ i → 0 ≤ᵣ x i) → 0 ≤ᵣ dot p x
dot-nonnegative p x p₊ x₊ =
  sum-nonnegative _ (λ i → nonnegative-mul (p i) (x i) (p₊ i) (x₊ i))

dot-left-add : ∀ {n} (p q x : Vector n) →
  dot (λ i → p i +ᵣ q i) x ≡ dot p x +ᵣ dot q x
dot-left-add p q x = sum-cong _ _ (λ i → ·DistR+ (p i) (q i) (x i))
  ∙ sum-add (λ i → p i ·ᵣ x i) (λ i → q i ·ᵣ x i)

dot-left-scale : ∀ {n} a (p x : Vector n) →
  dot (λ i → a ·ᵣ p i) x ≡ a ·ᵣ dot p x
dot-left-scale a p x = sum-cong _ _ (λ i → sym (·ᵣAssoc a (p i) (x i)))
  ∙ sum-scale a (λ i → p i ·ᵣ x i)

sum-exchange : ∀ {m n} (f : Fin m → Fin n → ℝ) →
  sum (λ i → sum (f i)) ≡ sum (λ j → sum (λ i → f i j))
sum-exchange {zero} {n} f = sym (sum-zero n)
sum-exchange {suc m} {n} f =
  cong (sum (f F.zero) +ᵣ_) (sum-exchange (λ i j → f (F.suc i) j))
  ∙ sym (sum-add (f F.zero) (λ j → sum (λ i → f (F.suc i) j)))
