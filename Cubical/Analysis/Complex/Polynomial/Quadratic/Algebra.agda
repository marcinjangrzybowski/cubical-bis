module Cubical.Analysis.Complex.Polynomial.Quadratic.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
open import Cubical.Data.Vec using (Vec; []; _∷_)
import Cubical.Analysis.Complex.Polynomial.MonicAlgebra as MonicDefinition

module Quadratic {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  private module M = MonicDefinition.Monic R

  boundFormula : ∀ a r → a + r · (0r + r · (1r + r · 0r)) ≡ a + r · r
  boundFormula a r = solve! R

  lipschitzFormula : ∀ r →
    (0r + r · (1r + r · 0r)) + r · ((1r + r · 0r) + r · (0r + r · 0r)) ≡ r + r
  lipschitzFormula r = solve! R

  fixedToRoot : ∀ c z → c + z · z ≡ z → c + z · ((- 1r) + z · 1r) ≡ 0r
  fixedToRoot c z fixed = (solve! R) ∙ cong (_- z) fixed ∙ +InvR z

  rootToFixed : ∀ c z → c + z · ((- 1r) + z · 1r) ≡ 0r → c + z · z ≡ z
  rootToFixed c z root = (solve! R) ∙ cong (_+ z) root ∙ +IdL z

  quadraticFactors : ∀ b h w → h + h ≡ 1r →
    M.linearFactors (((- (h · b)) + w) ∷ ((- (h · b)) - w) ∷ []) ≡
      ((h · b) · (h · b) - w · w) ∷ b ∷ []
  quadraticFactors b h w halves = cong₂ _∷_ (solve! R)
    (cong (_∷ []) (linearCoefficient ∙ cong (_· b) halves ∙ ·IdL b))
    where
    linearCoefficient : - ((- (h · b)) - w) + (- ((- (h · b)) + w)) ≡ (h + h) · b
    linearCoefficient = solve! R

  subtractTwice : ∀ x a → x - (x - a) ≡ a
  subtractTwice x a = solve! R
