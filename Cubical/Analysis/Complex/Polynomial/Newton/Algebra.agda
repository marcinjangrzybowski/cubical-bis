module Cubical.Analysis.Complex.Polynomial.Newton.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

module NewtonIdentities {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)

  correction : ∀ z inverse value → (z - inverse · value) - z ≡ - (inverse · value)
  correction z inverse value = solve! R

  aroundCenter : ∀ value middle center → value - center ≡ (value - middle) + (middle - center)
  aroundCenter value middle center = solve! R

  preserveRadius : ∀ q radius → q · radius + (1r - q) · radius ≡ radius
  preserveRadius q radius = solve! R

  private
    differenceStep : ∀ z w inverse pz pw →
      (z - inverse · pz) - (w - inverse · pw) ≡ 1r · (z - w) - inverse · (pz - pw)
    differenceStep z w inverse pz pw = solve! R

    remainderStep : ∀ z w inverse derivative pz pw →
      (inverse · derivative) · (z - w) - inverse · (pz - pw) ≡
      (- inverse) · ((pz - pw) - derivative · (z - w))
    remainderStep z w inverse derivative pz pw = solve! R

  difference : ∀ inverse derivative → inverse · derivative ≡ 1r → ∀ z w pz pw →
    (z - inverse · pz) - (w - inverse · pw) ≡
    (- inverse) · ((pz - pw) - derivative · (z - w))
  difference inverse derivative inverseLaw z w pz pw = differenceStep z w inverse pz pw
    ∙ cong (λ d → d · (z - w) - inverse · (pz - pw)) (sym inverseLaw)
    ∙ remainderStep z w inverse derivative pz pw

  rootToFixed : ∀ inverse z value → value ≡ 0r → z - inverse · value ≡ z
  rootToFixed inverse z value root = cong (λ v → z - inverse · v) root ∙ finish
    where
    finish : z - inverse · 0r ≡ z
    finish = solve! R

  private
    recover : ∀ inverse derivative z value →
      derivative · (z - (z - inverse · value)) ≡ (inverse · derivative) · value
    recover inverse derivative z value = solve! R

    zeroDifference : ∀ derivative z → derivative · (z - z) ≡ 0r
    zeroDifference derivative z = solve! R

  fixedToRoot : ∀ inverse derivative → inverse · derivative ≡ 1r → ∀ z value →
    z - inverse · value ≡ z → value ≡ 0r
  fixedToRoot inverse derivative inverseLaw z value fixed =
    sym (·IdL value)
    ∙ cong (_· value) (sym inverseLaw)
    ∙ sym (recover inverse derivative z value)
    ∙ cong (λ t → derivative · (z - t)) fixed
    ∙ zeroDifference derivative z
