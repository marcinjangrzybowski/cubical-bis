module Cubical.HITs.CauchyReals.Complex.Modulus.Positive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function

open import Cubical.Data.Sum
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive using
  (positiveMulClosed)
open import Cubical.HITs.CauchyReals.Algebra.Order.Apartness using
  (_＃_)
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base using
  (root)
open import Cubical.HITs.CauchyReals.Transcendental.Roots.NonNegative using
  (nth-rootNonNeg; nth-rootNonNegDef)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.NormSquared
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition


opaque
  0#ℂ→0<modulus : ∀ {z} → 0ℂ #ℂ z → 0 <ᵣ modulus z
  0#ℂ→0<modulus {z} 0#z =
    let 0<norm = 0#ℂ→0<normSq 0#z
        rootPath : modulus z ≡ fst (root 2 (normSq z , 0<norm))
        rootPath =
          cong (fst ∘ nth-rootNonNeg 2)
            (ℝ₀₊≡ {x = normSq₀₊ z}
              {y = normSq z , <ᵣWeaken≤ᵣ 0 (normSq z) 0<norm} refl)
          ∙ snd (fst (snd (nth-rootNonNegDef 2)))
              (normSq z , 0<norm)
    in subst (0 <ᵣ_) (sym rootPath) (snd (root 2 (normSq z , 0<norm)))


0<modulus→0#ℂ : ∀ {z} → 0 <ᵣ modulus z → 0ℂ #ℂ z
0<modulus→0#ℂ {z} 0<|z| = 0<normSq→0#ℂ
  (subst (0 <ᵣ_) (modulusSq z)
    (positiveMulClosed (modulus z) (modulus z) 0<|z| 0<|z|))


0#ℂ≃0<modulus : ∀ z → (0ℂ #ℂ z) ≃ (0 <ᵣ modulus z)
0#ℂ≃0<modulus z = propBiimpl→Equiv
  (isProp#ℂ _ _) (isProp<ᵣ _ _)
  0#ℂ→0<modulus 0<modulus→0#ℂ


0#modulus : ∀ {z} → 0ℂ #ℂ z → 0 ＃ modulus z
0#modulus 0#z = inl (0#ℂ→0<modulus 0#z)
