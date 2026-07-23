module Cubical.HITs.CauchyReals.Complex.Inverse.Laws where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Algebra.Inverse using
  (_＃_; invℝ; invℝ-pos; x·invℝ[x])

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Conjugation
open import Cubical.HITs.CauchyReals.Complex.NormSquared
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Inverse.Base

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


opaque
  inverseNorm-algebra : ∀ (x : ℝ) (0#x : rat 0 ＃ x) →
    (invℝ x 0#x ·ᵣ invℝ x 0#x) ·ᵣ x ≡ invℝ x 0#x
  inverseNorm-algebra x 0#x =
    let r = invℝ x 0#x
    in sym (·ᵣAssoc r r x)
      ∙ cong (r ·ᵣ_) (·ᵣComm r x)
      ∙ cong (r ·ᵣ_) (x·invℝ[x] x 0#x)
      ∙ Rℝ.·IdR r


opaque
  normSq-invℂ-expand : ∀ z (0#z : 0ℂ #ℂ z) →
    normSq (invℂ z 0#z) ≡
    (invℝ (normSq z) (normSqApart z 0#z) ·ᵣ
     invℝ (normSq z) (normSqApart z 0#z)) ·ᵣ normSq z
  normSq-invℂ-expand z 0#z =
    normSq-mul
      (fromℝ (invℝ (normSq z) (normSqApart z 0#z))) (conj z)
    ∙ cong₂ _·ᵣ_
        (normSq-fromℝ (invℝ (normSq z) (normSqApart z 0#z)))
        (normSq-conj z)


opaque
  normSq-invℂ : ∀ z (0#z : 0ℂ #ℂ z) →
    normSq (invℂ z 0#z) ≡
    invℝ (normSq z) (normSqApart z 0#z)
  normSq-invℂ z 0#z =
    normSq-invℂ-expand z 0#z
    ∙ inverseNorm-algebra (normSq z) (normSqApart z 0#z)


0#invℂ : ∀ z (0#z : 0ℂ #ℂ z) → 0ℂ #ℂ invℂ z 0#z
0#invℂ z 0#z = 0<normSq→0#ℂ
  (subst (0 <ᵣ_) (sym (normSq-invℂ z 0#z))
    (invℝ-pos (normSq z) (0#ℂ→0<normSq 0#z)))


opaque
  invℂ-invol : ∀ z (0#z : 0ℂ #ℂ z) →
    invℂ (invℂ z 0#z) (0#invℂ z 0#z) ≡ z
  invℂ-invol z 0#z =
    let b = invℂ z 0#z
        0#b = 0#invℂ z 0#z
        a = invℂ b 0#b
    in sym (·ℂIdR a)
      ∙ cong (a ·ℂ_) (sym (·invℂ z 0#z))
      ∙ ·ℂAssoc a z b
      ∙ cong (_·ℂ b) (·ℂComm a z)
      ∙ sym (·ℂAssoc z a b)
      ∙ cong (z ·ℂ_) (·ℂComm a b)
      ∙ cong (z ·ℂ_) (·invℂ b 0#b)
      ∙ ·ℂIdR z
