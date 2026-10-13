module Cubical.Analysis.Complex.FundamentalTheorem.Completion.Enumeration where

-- Explicit enumerations are used only for rational data. Surjectivity
-- stays truncated, which suffices for the finite least-witness search.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)
open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.Data.Rationals.NatIso using (ℚIsoℕ)
open import Cubical.Data.Vec using (Vec; []; _∷_)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Presented using (GaussianRational)

private
  pair : ℕ → ℕ → ℕ
  pair a b = Iso.fun ℕ×ℕ≅ℕ (a , b)

  unpair : ℕ → ℕ × ℕ
  unpair = Iso.inv ℕ×ℕ≅ℕ

  unpair-pair : ∀ a b → unpair (pair a b) ≡ (a , b)
  unpair-pair a b = Iso.ret ℕ×ℕ≅ℕ (a , b)

-- Reuse the library's constructive rational enumeration. The consumers
-- require only surjectivity, not a particular order of rational codes.
rationalEnumeration : ℕ → ℚ
rationalEnumeration = Iso.inv ℚIsoℕ

rationalEnumeration-surjective : ∀ q → PT.∥ Σ[ k ∈ ℕ ] (rationalEnumeration k ≡ q) ∥₁
rationalEnumeration-surjective q = PT.∣ Iso.fun ℚIsoℕ q , Iso.ret ℚIsoℕ q ∣₁

private
  gaussianPair : ℕ × ℕ → GaussianRational
  gaussianPair ab = rationalEnumeration (fst ab) , rationalEnumeration (snd ab)

gaussianEnumeration : ℕ → GaussianRational
gaussianEnumeration k = gaussianPair (unpair k)

gaussianEnumeration-surjective : ∀ q → PT.∥ Σ[ k ∈ ℕ ] (gaussianEnumeration k ≡ q) ∥₁
gaussianEnumeration-surjective (a , b) = PT.map2
  (λ { (i , ai) (j , bj) → pair i j ,
    cong gaussianPair (unpair-pair i j)
      ∙ (λ t → ai t , bj t) })
  (rationalEnumeration-surjective a) (rationalEnumeration-surjective b)

configurationEnumeration : ∀ n → ℕ → Vec GaussianRational n
configurationEnumeration zero k = []
configurationEnumeration (suc n) k =
  gaussianEnumeration (fst (unpair k)) ∷ configurationEnumeration n (snd (unpair k))

configurationEnumeration-surjective : ∀ {n} (qs : Vec GaussianRational n) →
  PT.∥ Σ[ k ∈ ℕ ] (configurationEnumeration n k ≡ qs) ∥₁
configurationEnumeration-surjective [] = PT.∣ zero , refl ∣₁
configurationEnumeration-surjective {suc n} (q ∷ qs) = PT.map2
  (λ { (i , qi) (j , qsj) → pair i j ,
    cong (λ ab → gaussianEnumeration (fst ab) ∷ configurationEnumeration n (snd ab)) (unpair-pair i j)
      ∙ cong₂ _∷_ qi qsj })
  (gaussianEnumeration-surjective q) (configurationEnumeration-surjective qs)
