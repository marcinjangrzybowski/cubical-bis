module Cubical.HITs.CauchyReals.Complex.Transcendental.Trigonometric where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals as ℚ using ([_/_])
open import Cubical.Data.NatPlusOne
import Cubical.Data.Int as ℤ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Trigonometry.Base using
  (sin; cos; sin-odd; cos-even)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Transcendental.Exponential

import Cubical.Algebra.CommRing as CR
open import Cubical.Tactics.CommRingSolver
open import Cubical.Tactics.CommRingSolver.Specialised.Reals


module RingIdentities {ℓ} (R' : CR.CommRing ℓ) where
  private
    R = fst R'

  open CR.CommRingStr (snd R')

  opaque
    rearrange-product : ∀ h k a b c d →
      (h · (a + b)) · (h · (c + d)) +
        (- ((k · (a + (- b))) · (k · (c + (- d))))) ≡
      (h · h) · ((a + b) · (c + d)) +
        (- ((k · k) · ((a + (- b)) · (c + (- d)))))
    rearrange-product h k a b c d = solve! R'

  opaque
    collect-conjugate-products : ∀ h a b c d →
      h · ((a + b) · (c + d)) +
        (- ((- h) · ((a + (- b)) · (c + (- d))))) ≡
      (h + h) · (a · c + b · d)
    collect-conjugate-products h a b c d = solve! R'

  opaque
    combine-sine-products : ∀ h k a b c d →
      (k · (a + (- b))) · (h · (c + d)) +
        (h · (a + b)) · (k · (c + (- d))) ≡
      (k · (h + h)) · (a · c + (- (b · d)))
    combine-sine-products h k a b c d = solve! R'

  opaque
    rearrange-square-products : ∀ h k a b →
      (h · (a + b)) · (h · (a + b)) +
        (k · (a + (- b))) · (k · (a + (- b))) ≡
      (h · h) · ((a + b) · (a + b)) +
        (k · k) · ((a + (- b)) · (a + (- b)))
    rearrange-square-products h k a b = solve! R'

  opaque
    collect-square-difference : ∀ h a b →
      h · ((a + b) · (a + b)) +
        (- h) · ((a + (- b)) · (a + (- b))) ≡
      ((h + h) + (h + h)) · (a · b)
    collect-square-difference h a b = solve! R'


halfℝ : ℝ
halfℝ = rat [ 1 / 2 ]


halfℂ : ℂ
halfℂ = fromℝ halfℝ


cosFromExp : ℂ → ℂ → ℂ
cosFromExp A B = halfℂ ·ℂ (A +ℂ B)


sinFromExp : ℂ → ℂ → ℂ
sinFromExp A B = ((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (A -ℂ B)


cosℂ : ℂ → ℂ
cosℂ z = cosFromExp (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z)))


sinℂ : ℂ → ℂ
sinℂ z = sinFromExp (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z)))


opaque
  euler-algebra : ∀ A B →
    cosFromExp A B +ℂ iℂ ·ℂ sinFromExp A B ≡ A
  euler-algebra _ _ = ℂ≡ ℝ! ℝ!


euler-decomposition : ∀ z →
  expℂ (iℂ ·ℂ z) ≡ cosℂ z +ℂ iℂ ·ℂ sinℂ z
euler-decomposition z = sym (euler-algebra
  (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z))))


opaque
  cosFromExp-swap : ∀ A B → cosFromExp B A ≡ cosFromExp A B
  cosFromExp-swap _ _ = ℂ≡ ℝ! ℝ!


opaque
  sinFromExp-swap : ∀ A B → sinFromExp B A ≡ -ℂ sinFromExp A B
  sinFromExp-swap _ _ = ℂ≡ ℝ! ℝ!


opaque
  negIHalf-square :
    ((-ℂ iℂ) ·ℂ halfℂ) ·ℂ ((-ℂ iℂ) ·ℂ halfℂ) ≡
      -ℂ (halfℂ ·ℂ halfℂ)
  negIHalf-square = ℂ≡ ℝ! ℝ!


opaque
  double-half-square :
    halfℂ ·ℂ halfℂ +ℂ halfℂ ·ℂ halfℂ ≡ halfℂ
  double-half-square = ℂ≡ ℝ! ℝ!


opaque
  double-half : halfℂ +ℂ halfℂ ≡ 1ℂ
  double-half = ℂ≡ ℝ! ℝ!


opaque
  quadruple-half-square :
    (halfℂ ·ℂ halfℂ +ℂ halfℂ ·ℂ halfℂ) +ℂ
    (halfℂ ·ℂ halfℂ +ℂ halfℂ ·ℂ halfℂ) ≡ 1ℂ
  quadruple-half-square =
    cong₂ _+ℂ_ double-half-square double-half-square ∙ double-half


opaque
  cosProduct-algebra : ∀ A B C D →
    (halfℂ ·ℂ (A +ℂ B)) ·ℂ (halfℂ ·ℂ (C +ℂ D)) -ℂ
    (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (A -ℂ B)) ·ℂ
      (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (C -ℂ D)) ≡
    halfℂ ·ℂ (A ·ℂ C +ℂ B ·ℂ D)
  cosProduct-algebra A B C D =
    (halfℂ ·ℂ (A +ℂ B)) ·ℂ (halfℂ ·ℂ (C +ℂ D)) -ℂ
      (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (A -ℂ B)) ·ℂ
        (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (C -ℂ D))
      ≡⟨ RingIdentities.rearrange-product ℂcommRing
          halfℂ ((-ℂ iℂ) ·ℂ halfℂ) A B C D ⟩
    (halfℂ ·ℂ halfℂ) ·ℂ ((A +ℂ B) ·ℂ (C +ℂ D)) -ℂ
      (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ ((-ℂ iℂ) ·ℂ halfℂ)) ·ℂ
        ((A -ℂ B) ·ℂ (C -ℂ D))
      ≡⟨ cong
          (λ q →
            (halfℂ ·ℂ halfℂ) ·ℂ ((A +ℂ B) ·ℂ (C +ℂ D)) -ℂ
              q ·ℂ ((A -ℂ B) ·ℂ (C -ℂ D)))
          negIHalf-square ⟩
    (halfℂ ·ℂ halfℂ) ·ℂ ((A +ℂ B) ·ℂ (C +ℂ D)) -ℂ
      (-ℂ (halfℂ ·ℂ halfℂ)) ·ℂ ((A -ℂ B) ·ℂ (C -ℂ D))
      ≡⟨ RingIdentities.collect-conjugate-products ℂcommRing
          (halfℂ ·ℂ halfℂ) A B C D ⟩
    (halfℂ ·ℂ halfℂ +ℂ halfℂ ·ℂ halfℂ) ·ℂ
      (A ·ℂ C +ℂ B ·ℂ D)
      ≡⟨ cong (λ q → q ·ℂ (A ·ℂ C +ℂ B ·ℂ D))
          double-half-square ⟩
    halfℂ ·ℂ (A ·ℂ C +ℂ B ·ℂ D) ∎


opaque
  cosFromExp-mul : ∀ A B C D →
    cosFromExp (A ·ℂ C) (B ·ℂ D) ≡
    cosFromExp A B ·ℂ cosFromExp C D -ℂ
    sinFromExp A B ·ℂ sinFromExp C D
  cosFromExp-mul A B C D = sym (cosProduct-algebra A B C D)


opaque
  sinProduct-algebra : ∀ A B C D →
    (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (A -ℂ B)) ·ℂ
      (halfℂ ·ℂ (C +ℂ D)) +ℂ
    (halfℂ ·ℂ (A +ℂ B)) ·ℂ
      (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (C -ℂ D)) ≡
    ((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (A ·ℂ C -ℂ B ·ℂ D)
  sinProduct-algebra A B C D =
    (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (A -ℂ B)) ·ℂ
        (halfℂ ·ℂ (C +ℂ D)) +ℂ
      (halfℂ ·ℂ (A +ℂ B)) ·ℂ
        (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (C -ℂ D))
      ≡⟨ RingIdentities.combine-sine-products ℂcommRing
          halfℂ ((-ℂ iℂ) ·ℂ halfℂ) A B C D ⟩
    (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (halfℂ +ℂ halfℂ)) ·ℂ
      (A ·ℂ C -ℂ B ·ℂ D)
      ≡⟨ cong
          (λ q → (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ q) ·ℂ
            (A ·ℂ C -ℂ B ·ℂ D))
          double-half ⟩
    (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ 1ℂ) ·ℂ
      (A ·ℂ C -ℂ B ·ℂ D)
      ≡⟨ cong (_·ℂ (A ·ℂ C -ℂ B ·ℂ D))
          (·ℂIdR ((-ℂ iℂ) ·ℂ halfℂ)) ⟩
    ((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (A ·ℂ C -ℂ B ·ℂ D) ∎


opaque
  sinFromExp-mul : ∀ A B C D →
    sinFromExp (A ·ℂ C) (B ·ℂ D) ≡
    sinFromExp A B ·ℂ cosFromExp C D +ℂ
    cosFromExp A B ·ℂ sinFromExp C D
  sinFromExp-mul A B C D = sym (sinProduct-algebra A B C D)


opaque
  pythagoreanProduct-algebra : ∀ A B →
    (halfℂ ·ℂ (A +ℂ B)) ·ℂ (halfℂ ·ℂ (A +ℂ B)) +ℂ
    (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (A -ℂ B)) ·ℂ
      (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (A -ℂ B)) ≡ A ·ℂ B
  pythagoreanProduct-algebra A B =
    (halfℂ ·ℂ (A +ℂ B)) ·ℂ (halfℂ ·ℂ (A +ℂ B)) +ℂ
      (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (A -ℂ B)) ·ℂ
        (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ (A -ℂ B))
      ≡⟨ RingIdentities.rearrange-square-products ℂcommRing
          halfℂ ((-ℂ iℂ) ·ℂ halfℂ) A B ⟩
    (halfℂ ·ℂ halfℂ) ·ℂ ((A +ℂ B) ·ℂ (A +ℂ B)) +ℂ
      (((-ℂ iℂ) ·ℂ halfℂ) ·ℂ ((-ℂ iℂ) ·ℂ halfℂ)) ·ℂ
        ((A -ℂ B) ·ℂ (A -ℂ B))
      ≡⟨ cong
          (λ q →
            (halfℂ ·ℂ halfℂ) ·ℂ ((A +ℂ B) ·ℂ (A +ℂ B)) +ℂ
              q ·ℂ ((A -ℂ B) ·ℂ (A -ℂ B)))
          negIHalf-square ⟩
    (halfℂ ·ℂ halfℂ) ·ℂ ((A +ℂ B) ·ℂ (A +ℂ B)) +ℂ
      (-ℂ (halfℂ ·ℂ halfℂ)) ·ℂ ((A -ℂ B) ·ℂ (A -ℂ B))
      ≡⟨ RingIdentities.collect-square-difference ℂcommRing
          (halfℂ ·ℂ halfℂ) A B ⟩
    ((halfℂ ·ℂ halfℂ +ℂ halfℂ ·ℂ halfℂ) +ℂ
      (halfℂ ·ℂ halfℂ +ℂ halfℂ ·ℂ halfℂ)) ·ℂ (A ·ℂ B)
      ≡⟨ cong (λ q → q ·ℂ (A ·ℂ B)) quadruple-half-square ⟩
    1ℂ ·ℂ (A ·ℂ B)
      ≡⟨ Cℂ.·IdL (A ·ℂ B) ⟩
    A ·ℂ B ∎


opaque
  pythagorean-algebra : ∀ A B →
    cosFromExp A B ·ℂ cosFromExp A B +ℂ
    sinFromExp A B ·ℂ sinFromExp A B ≡ A ·ℂ B
  pythagorean-algebra A B = pythagoreanProduct-algebra A B


i-neg-path : ∀ z → iℂ ·ℂ (-ℂ z) ≡ -ℂ (iℂ ·ℂ z)
i-neg-path _ = ℂ≡ ℝ! ℝ!


neg-i-neg-path : ∀ z → -ℂ (iℂ ·ℂ (-ℂ z)) ≡ iℂ ·ℂ z
neg-i-neg-path _ = ℂ≡ ℝ! ℝ!


cosℂ-neg : ∀ z → cosℂ (-ℂ z) ≡ cosℂ z
cosℂ-neg z =
  cong₂ cosFromExp
    (cong expℂ (i-neg-path z))
    (cong expℂ (neg-i-neg-path z))
  ∙ cosFromExp-swap _ _


sinℂ-neg : ∀ z → sinℂ (-ℂ z) ≡ -ℂ sinℂ z
sinℂ-neg z =
  cong₂ sinFromExp
    (cong expℂ (i-neg-path z))
    (cong expℂ (neg-i-neg-path z))
  ∙ sinFromExp-swap _ _


i-add-path : ∀ z w →
  iℂ ·ℂ (z +ℂ w) ≡ iℂ ·ℂ z +ℂ iℂ ·ℂ w
i-add-path z w = ·ℂDistR+ iℂ z w


neg-i-add-path : ∀ z w →
  -ℂ (iℂ ·ℂ (z +ℂ w)) ≡
  (-ℂ (iℂ ·ℂ z)) +ℂ (-ℂ (iℂ ·ℂ w))
neg-i-add-path _ _ = ℂ≡ ℝ! ℝ!


exp-i-add : ∀ z w →
  expℂ (iℂ ·ℂ (z +ℂ w)) ≡
  expℂ (iℂ ·ℂ z) ·ℂ expℂ (iℂ ·ℂ w)
exp-i-add z w = cong expℂ (i-add-path z w)
  ∙ expℂ-add (iℂ ·ℂ z) (iℂ ·ℂ w)


exp-neg-i-add : ∀ z w →
  expℂ (-ℂ (iℂ ·ℂ (z +ℂ w))) ≡
  expℂ (-ℂ (iℂ ·ℂ z)) ·ℂ expℂ (-ℂ (iℂ ·ℂ w))
exp-neg-i-add z w = cong expℂ (neg-i-add-path z w)
  ∙ expℂ-add (-ℂ (iℂ ·ℂ z)) (-ℂ (iℂ ·ℂ w))


cosℂ-add : ∀ z w →
  cosℂ (z +ℂ w) ≡ cosℂ z ·ℂ cosℂ w -ℂ sinℂ z ·ℂ sinℂ w
cosℂ-add z w = cong₂ cosFromExp (exp-i-add z w) (exp-neg-i-add z w)
  ∙ cosFromExp-mul _ _ _ _


sinℂ-add : ∀ z w →
  sinℂ (z +ℂ w) ≡ sinℂ z ·ℂ cosℂ w +ℂ cosℂ z ·ℂ sinℂ w
sinℂ-add z w = cong₂ sinFromExp (exp-i-add z w) (exp-neg-i-add z w)
  ∙ sinFromExp-mul _ _ _ _


cosℂ²+sinℂ² : ∀ z →
  cosℂ z ·ℂ cosℂ z +ℂ sinℂ z ·ℂ sinℂ z ≡ 1ℂ
cosℂ²+sinℂ² z =
  pythagorean-algebra
    (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z)))
  ∙ expℂ-neg-inverse (iℂ ·ℂ z)


exp-i-real : ∀ x → expℂ (iℂ ·ℂ fromℝ x) ≡ cis x
exp-i-real x = cong expℂ (ℂ≡ ℝ! ℝ!) ∙ euler-complex x


exp-neg-i-real : ∀ x → expℂ (-ℂ (iℂ ·ℂ fromℝ x)) ≡ cis (-ᵣ x)
exp-neg-i-real x = cong expℂ (ℂ≡ ℝ! ℝ!) ∙ euler-complex (-ᵣ x)


opaque
  sinFrom-cis-re-unfold : ∀ x →
    re (sinFromExp (cis x) (cis (-ᵣ x))) ≡
      halfℝ ·ᵣ (sin x -ᵣ sin (-ᵣ x))
  sinFrom-cis-re-unfold x = ℝ!

  sinFrom-cis-re-odd : ∀ x →
    halfℝ ·ᵣ (sin x -ᵣ sin (-ᵣ x)) ≡
      halfℝ ·ᵣ (sin x -ᵣ (-ᵣ sin x))
  sinFrom-cis-re-odd x = cong (halfℝ ·ᵣ_)
    (cong (λ y → sin x -ᵣ y) (sym (sin-odd x)))

  sinFrom-cis-re-end : ∀ x →
    halfℝ ·ᵣ (sin x -ᵣ (-ᵣ sin x)) ≡ sin x
  sinFrom-cis-re-end x = ℝ!

  sinFrom-cis-im-unfold : ∀ x →
    im (sinFromExp (cis x) (cis (-ᵣ x))) ≡
      (-ᵣ halfℝ) ·ᵣ (cos x -ᵣ cos (-ᵣ x))
  sinFrom-cis-im-unfold x = ℝ!

  sinFrom-cis-im-even : ∀ x →
    (-ᵣ halfℝ) ·ᵣ (cos x -ᵣ cos (-ᵣ x)) ≡
      (-ᵣ halfℝ) ·ᵣ (cos x -ᵣ cos x)
  sinFrom-cis-im-even x = cong ((-ᵣ halfℝ) ·ᵣ_)
    (cong (λ y → cos x -ᵣ y) (sym (cos-even x)))

  sinFrom-cis-im-end : ∀ x →
    (-ᵣ halfℝ) ·ᵣ (cos x -ᵣ cos x) ≡ 0
  sinFrom-cis-im-end x = ℝ!


opaque
  cosFrom-cis : ∀ x → cosFromExp (cis x) (cis (-ᵣ x)) ≡ fromℝ (cos x)
  cosFrom-cis x = ℂ≡
    (ℝ! ∙ cong (halfℝ ·ᵣ_)
      (cong (cos x +ᵣ_) (sym (cos-even x))) ∙ ℝ!)
    (ℝ! ∙ cong (halfℝ ·ᵣ_)
      (cong (sin x +ᵣ_) (sym (sin-odd x))) ∙ ℝ!)

  sinFrom-cis : ∀ x → sinFromExp (cis x) (cis (-ᵣ x)) ≡ fromℝ (sin x)
  sinFrom-cis x = ℂ≡
    (sinFrom-cis-re-unfold x
      ∙ sinFrom-cis-re-odd x
      ∙ sinFrom-cis-re-end x)
    (sinFrom-cis-im-unfold x
      ∙ sinFrom-cis-im-even x
      ∙ sinFrom-cis-im-end x)


cosℂ-real : ∀ x → cosℂ (fromℝ x) ≡ fromℝ (cos x)
cosℂ-real x = cong₂ cosFromExp (exp-i-real x) (exp-neg-i-real x)
  ∙ cosFrom-cis x


sinℂ-real : ∀ x → sinℂ (fromℝ x) ≡ fromℝ (sin x)
sinℂ-real x = cong₂ sinFromExp (exp-i-real x) (exp-neg-i-real x)
  ∙ sinFrom-cis x
