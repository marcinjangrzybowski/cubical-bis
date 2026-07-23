module Cubical.HITs.CauchyReals.Complex.Inverse.Formula where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Algebra.Inverse using (invℝ)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.NormSquared
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Inverse.Definition

opaque
  invℂ-formula : ∀ a b (0#z : 0ℂ #ℂ (a , b)) →
    invℂ (a , b) 0#z ≡
    ((a ·ᵣ invℝ (normSq (a , b)) (normSqApart (a , b) 0#z)) ,
     (-ᵣ b ·ᵣ invℝ (normSq (a , b)) (normSqApart (a , b) 0#z)))
  invℂ-formula a b 0#z = ℂ≡ real-part imaginary-part
    where
    r : ℝ
    r = invℝ (normSq (a , b)) (normSqApart (a , b) 0#z)

    real-part : r ·ᵣ a -ᵣ 0 ·ᵣ (-ᵣ b) ≡ a ·ᵣ r
    real-part =
      cong (λ x → r ·ᵣ a -ᵣ x) (Rℝ.0LeftAnnihilates (-ᵣ b))
      ∙ Rℝ.+IdR' (r ·ᵣ a) (-ᵣ 0) (-ᵣ-rat 0)
      ∙ ·ᵣComm r a

    imaginary-part : r ·ᵣ (-ᵣ b) +ᵣ 0 ·ᵣ a ≡ (-ᵣ b) ·ᵣ r
    imaginary-part =
      cong (λ x → r ·ᵣ (-ᵣ b) +ᵣ x) (Rℝ.0LeftAnnihilates a)
      ∙ Rℝ.+IdR (r ·ᵣ (-ᵣ b))
      ∙ ·ᵣComm r (-ᵣ b)
