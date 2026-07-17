module Cubical.HITs.CauchyReals.Algebra.Ring where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

import Cubical.Algebra.CommRing as CR
import Cubical.Algebra.Ring as RP

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Algebra.Multiplication


module Rℝ where
  ℝRing = CR.CommRing→Ring ℝcommRing
  open CR.CommRingStr (snd ℝcommRing) public
  open RP.RingTheory ℝRing public
  open CR.CommRingTheory ℝcommRing public


-ᵣ≡[-1·ᵣ] : ∀ x → -ᵣ x ≡ (-1) ·ᵣ x
-ᵣ≡[-1·ᵣ] x =
  Rℝ.-IsMult-1 x ∙ cong (_·ᵣ x) (-ᵣ-rat 1)
