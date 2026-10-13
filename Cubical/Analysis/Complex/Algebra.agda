module Cubical.Analysis.Complex.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RP
open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Algebra.CommRing using (ℝCommRing)
open import Cubical.Analysis.Complex.Base
import Cubical.Analysis.Complex.Algebra.Cartesian as CartesianDefinition

open CartesianDefinition.Cartesian ℝCommRing public
  using (0ℂ; 1ℂ; iℂ; _+ℂ_; -ℂ_; _-ℂ_; _·ℂ_;
    +ℂAssoc; +ℂIdR; +ℂInvR; +ℂComm;
    ·ℂAssoc; ·ℂIdR; ·ℂDistR+; ·ℂComm; i²≡-1)
  renaming (embed to fromℝ; pairCommRing to ℂCommRing;
    embed-pres+ to fromℝ-pres+; embed-pres· to fromℝ-pres·;
    embedHom to realToComplexHom)

module ℂRing = RP.RingTheory (CommRing→Ring ℂCommRing)

open Exponentiation ℂCommRing public using () renaming (_^_ to _^ℂ_)

fromℚ : ℚ → ℂ
fromℚ q = fromℝ (rat q)
