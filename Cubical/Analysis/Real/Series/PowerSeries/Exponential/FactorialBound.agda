module Cubical.Analysis.Real.Series.PowerSeries.Exponential.FactorialBound where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
  using (ℕ; zero; suc; _+_; _·_; _^_; _!)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Rationals.Base as ℚ
  using (ℚ; fromNat)
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra
  using (_^ⁿ_; _ℚ₊^ⁿ_; fromNat-^)
import Cubical.Data.Rationals.Inverse as ℚInv

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; _·₊_)
open ℚInv using (_⁻¹₊)

open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients


private
  -- Once the index has reached B, every further factorial factor is at
  -- least B.  This is the discrete core of the geometric majorant.
  factorialPowerBound-after : ∀ b offset →
    let base = suc b
        index = offset + base
    in base ^ index ℕ.≤ (index !) · base ^ base
  factorialPowerBound-after b zero =
    subst
      (ℕ._≤ ((suc b) !) · (suc b) ^ suc b)
      (ℕ.·-identityˡ ((suc b) ^ suc b))
      (ℕ.≤-·k (ℕ.0<! (suc b)))
  factorialPowerBound-after b (suc offset) =
    ℕ.≤-trans
      (ℕ.≤-k· {k = suc b}
        (factorialPowerBound-after b offset))
      (subst
        (ℕ._≤
          (suc (offset + suc b) · ((offset + suc b) !)) ·
            (suc b) ^ suc b)
        (sym
          (ℕ.·-assoc
            (suc b)
            ((offset + suc b) !)
            ((suc b) ^ suc b)))
        (ℕ.≤-·k scaledFactorial))
    where
    base≤nextIndex : suc b ℕ.≤ suc (offset + suc b)
    base≤nextIndex = suc offset , refl

    scaledFactorial :
      suc b · ((offset + suc b) !)
        ℕ.≤ suc (offset + suc b) · ((offset + suc b) !)
    scaledFactorial = ℕ.≤-·k base≤nextIndex

  power≤basePower : ∀ b n → n ℕ.≤ suc b →
    (suc b) ^ n ℕ.≤ (suc b) ^ suc b
  power≤basePower b zero n≤base =
    ℕ.≤-trans
      (subst (1 ℕ.≤_)
        (sym (ℕ.·-identityʳ (suc b)))
        (ℕ.suc-≤-suc ℕ.zero-≤))
      (ℕ.^-monotone (suc b) zero b ℕ.zero-≤)
  power≤basePower b (suc k) n≤base =
    ℕ.^-monotone (suc b) k b
      (ℕ.predℕ-≤-predℕ n≤base)

  factorialPowerBound-before : ∀ b n → n ℕ.≤ suc b →
    (suc b) ^ n ℕ.≤ (n !) · (suc b) ^ suc b
  factorialPowerBound-before b n n≤base =
    ℕ.≤-trans (power≤basePower b n n≤base)
      (subst
        (ℕ._≤ (n !) · (suc b) ^ suc b)
        (ℕ.·-identityˡ ((suc b) ^ suc b))
        (ℕ.≤-·k (ℕ.0<! n)))


-- A parameterized factorial estimate.  The base is represented as suc b,
-- so positivity is structural and no nonzero side condition is needed.
exponentialFactorialPowerBound : ∀ b n →
  (suc b) ^ n ℕ.≤ (n !) · (suc b) ^ suc b
exponentialFactorialPowerBound b n with ℕ.splitℕ-≤ n (suc b)
... | inl n≤base = factorialPowerBound-before b n n≤base
... | inr base<n =
  subst
    (λ index →
      (suc b) ^ index ℕ.≤ (index !) · (suc b) ^ suc b)
    (ℕ.≤-∸-+-cancel (ℕ.<-weaken base<n))
    (factorialPowerBound-after b (n ℕ.∸ suc b))


-- The corresponding exact-rational geometric majorant has decay 1/B and
-- prefactor B^B.  These positive presentations are consumed directly by
-- the power-series growth API.
exponentialFactorialGrowthBound : ℕ → ℚ₊
exponentialFactorialGrowthBound b =
  exponentialPositiveNatural b ℚ₊^ⁿ suc b


exponentialFactorialDecay : ℕ → ℚ₊
exponentialFactorialDecay b =
  exponentialPositiveNatural b ⁻¹₊


private
  module ℚOrder =
    OrderedCommRingTheory ℚOrderedCommRing

  fromNat-mono : ∀ {m n} →
    m ℕ.≤ n → ℚ.fromNat m ℚ.≤ ℚ.fromNat n
  fromNat-mono {m} {n} (difference , difference+m≡n) =
    subst (ℚ.fromNat m ℚ.≤_)
      (ℚ.ℕ+→ℚ+ difference m
      ∙ cong (λ k → ℚ.fromNat k) difference+m≡n)
      (subst2 ℚ._≤_
        (ℚ.+IdR (ℚ.fromNat m))
        (ℚ.+Comm (ℚ.fromNat m) (ℚ.fromNat difference))
        (ℚOrder.+MonoL≤
          0 (ℚ.fromNat difference) (ℚ.fromNat m)
          (ℚ.0≤pos difference (1+ zero))))

  powℚPath : ∀ q n →
    powℚ q n ≡ q ^ⁿ n
  powℚPath q zero = refl
  powℚPath q (suc n) =
    cong (q ℚ.·_) (powℚPath q n)

  embeddedFactorialPowerBound : ∀ b n →
    fst (exponentialPositiveNatural b ℚ₊^ⁿ n) ℚ.≤
    fst
      (exponentialRationalFactorial n ·₊
        exponentialFactorialGrowthBound b)
  embeddedFactorialPowerBound b n =
    subst2 ℚ._≤_
      (sym (fromNat-^ (suc b) n))
      (sym productPath)
      (fromNat-mono (exponentialFactorialPowerBound b n))
    where
    productPath :
      fst
        (exponentialRationalFactorial n ·₊
          exponentialFactorialGrowthBound b)
        ≡
      ℚ.fromNat ((n !) · (suc b) ^ suc b)
    productPath =
      cong₂ ℚ._·_
        (exponentialRationalFactorial-value n)
        (fromNat-^ (suc b) (suc b))
      ∙ ℚ.ℕ·→ℚ· (n !) ((suc b) ^ suc b)


-- Exact-rational form of 1/n! ≤ B^B (1/B)^n, where B = suc b.
exponentialRationalCoefficient-factorialGrowth : ∀ b n →
  exponentialRationalCoefficient n ℚ.≤
  fst (exponentialFactorialGrowthBound b) ℚ.·
    powℚ (fst (exponentialFactorialDecay b)) n
exponentialRationalCoefficient-factorialGrowth b n =
  subst2 ℚ._≤_ leftPath rightPath multipliedInverseBound
  where
  base : ℚ₊
  base = exponentialPositiveNatural b

  basePower : ℚ₊
  basePower = base ℚ₊^ⁿ n

  growthBound : ℚ₊
  growthBound = exponentialFactorialGrowthBound b

  factorialGrowth : ℚ₊
  factorialGrowth =
    exponentialRationalFactorial n ·₊ growthBound

  inverseBound :
    fst (factorialGrowth ⁻¹₊) ℚ.≤ fst (basePower ⁻¹₊)
  inverseBound =
    ℚInv.invℚ₊≤invℚ₊ factorialGrowth basePower
      (embeddedFactorialPowerBound b n)

  multipliedInverseBound :
    fst growthBound ℚ.· fst (factorialGrowth ⁻¹₊) ℚ.≤
    fst growthBound ℚ.· fst (basePower ⁻¹₊)
  multipliedInverseBound =
    ℚOrder.·MonoL≤
      (fst (factorialGrowth ⁻¹₊))
      (fst (basePower ⁻¹₊))
      (fst growthBound)
      (ℚ.<Weaken≤ 0 (fst growthBound) (snd growthBound))
      inverseBound

  leftPath :
    fst growthBound ℚ.· fst (factorialGrowth ⁻¹₊)
      ≡ exponentialRationalCoefficient n
  leftPath =
    cong (fst growthBound ℚ.·_)
      (cong fst
        (sym
          (ℚInv.invℚ₊Dist·
            (exponentialRationalFactorial n) growthBound)))
    ∙ ℚ.·Assoc
        (fst growthBound)
        (exponentialRationalCoefficient n)
        (fst (growthBound ⁻¹₊))
    ∙ cong (ℚ._· fst (growthBound ⁻¹₊))
        (ℚ.·Comm
          (fst growthBound)
          (exponentialRationalCoefficient n))
    ∙ sym
        (ℚ.·Assoc
          (exponentialRationalCoefficient n)
          (fst growthBound)
          (fst (growthBound ⁻¹₊)))
    ∙ cong (exponentialRationalCoefficient n ℚ.·_)
        (ℚInv.x·invℚ₊[x] growthBound)
    ∙ ℚ.·IdR (exponentialRationalCoefficient n)

  rightPath :
    fst growthBound ℚ.· fst (basePower ⁻¹₊)
      ≡
    fst growthBound ℚ.·
      powℚ (fst (exponentialFactorialDecay b)) n
  rightPath =
    cong (fst growthBound ℚ.·_)
      (ℚInv.invℚ₊-ℚ^ⁿ base n)
    ∙ cong (fst growthBound ℚ.·_)
        (sym (powℚPath (fst (exponentialFactorialDecay b)) n))
