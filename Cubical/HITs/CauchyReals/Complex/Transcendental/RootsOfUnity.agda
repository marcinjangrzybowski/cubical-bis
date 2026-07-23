module Cubical.HITs.CauchyReals.Complex.Transcendental.RootsOfUnity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ hiding (_+_; _·_)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base using
  (/nᵣ; /nᵣ-／ᵣ₊; seqSumUpTo; seqSumUpToConst)
open import Cubical.HITs.CauchyReals.Trigonometry.Base using
  (sin; cos; sin0=0; cos0=1)
open import Cubical.HITs.CauchyReals.Trigonometry.Pi using
  (π-number)
open import Cubical.HITs.CauchyReals.Trigonometry.Identities using
  (sin-period; cos-period)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Transcendental.Cis


twoPi : ℝ
twoPi = 2 ·ᵣ π-number


angleMultiple : ℕ → ℝ → ℝ
angleMultiple n x = seqSumUpTo (const x) n


cis-power : ∀ x n → cis x ^ℂ n ≡ cis (angleMultiple n x)
cis-power x zero = sym cis0
cis-power x (suc n) =
  cong (cis x ·ℂ_) (cis-power x n)
  ∙ sym (cis-add x (angleMultiple n x))


cis-twoPi : cis twoPi ≡ 1ℂ
cis-twoPi = ℂ≡
  (cong cos (sym (Rℝ.+IdL twoPi)) ∙ cos-period 0 ∙ cos0=1)
  (cong sin (sym (Rℝ.+IdL twoPi)) ∙ sin-period 0 ∙ sin0=0)


positiveNatReal : ℕ₊₁ → ℝ₊
positiveNatReal n = fromNat (ℕ₊₁→ℕ n)


rootAngle : ℕ₊₁ → ℝ
rootAngle n = /nᵣ n twoPi


angleMultiple-rootAngle : ∀ n →
  angleMultiple (ℕ₊₁→ℕ n) (rootAngle n) ≡ twoPi
angleMultiple-rootAngle n =
  seqSumUpToConst (rootAngle n) (ℕ₊₁→ℕ n)
  ∙ cong (_·ᵣ fst (positiveNatReal n)) (/nᵣ-／ᵣ₊ n twoPi)
  ∙ [x/₊y]·yᵣ twoPi (positiveNatReal n)


IsRootOfUnity : ℕ₊₁ → ℂ → Type₀
IsRootOfUnity n z = z ^ℂ (ℕ₊₁→ℕ n) ≡ 1ℂ


RootOfUnity : ℕ₊₁ → Type₀
RootOfUnity n = Σ[ z ∈ ℂ ] IsRootOfUnity n z


principalRoot : ℕ₊₁ → ℂ
principalRoot n = cis (rootAngle n)


principalRootIsRoot : ∀ n → IsRootOfUnity n (principalRoot n)
principalRootIsRoot n =
  cis-power (rootAngle n) (ℕ₊₁→ℕ n)
  ∙ cong cis (angleMultiple-rootAngle n)
  ∙ cis-twoPi


principalRootOfUnity : ∀ n → RootOfUnity n
principalRootOfUnity n = principalRoot n , principalRootIsRoot n


rootPower : ℕ₊₁ → ℕ → ℂ
rootPower n k = principalRoot n ^ℂ k


rootPowerIsRoot : ∀ n k → IsRootOfUnity n (rootPower n k)
rootPowerIsRoot n k =
  sym (Exponentiationℂ.^-rdist-·ℕ
    (principalRoot n) k (ℕ₊₁→ℕ n))
  ∙ cong (principalRoot n ^ℂ_) (ℕ.·-comm k (ℕ₊₁→ℕ n))
  ∙ Exponentiationℂ.^-rdist-·ℕ
      (principalRoot n) (ℕ₊₁→ℕ n) k
  ∙ cong (_^ℂ k) (principalRootIsRoot n)
  ∙ Exponentiationℂ.1ⁿ≡1 k


rootPowerOfUnity : ∀ n k → RootOfUnity n
rootPowerOfUnity n k = rootPower n k , rootPowerIsRoot n k
