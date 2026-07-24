module Cubical.HITs.CauchyReals.Complex.Calculus.LocalBound where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.Zero
open import Cubical.HITs.CauchyReals.Complex.Modulus.Bounds
open import Cubical.HITs.CauchyReals.Complex.Modulus.TriangleInequality
open import Cubical.HITs.CauchyReals.Complex.Domain


ComplexLocalBoundWithinAt :
  ComplexPredicate → (ℂ → ℂ) → ℂ → Type₀
ComplexLocalBoundWithinAt P f z =
  Σ[ radius ∈ ℚ₊ ]
  Σ[ bound ∈ ℚ₊ ]
    ((h : ℂ) → z +ℂ h ∈ P →
      modulus h <ᵣ rat (fst radius) →
      modulus (f (z +ℂ h))
        ≤ᵣ rat (fst bound))


ComplexLocallyBoundedWithin :
  ComplexPredicate → (ℂ → ℂ) → Type₀
ComplexLocallyBoundedWithin P f =
  (z : ℂ) → z ∈ P → ComplexLocalBoundWithinAt P f z


ComplexLocallyBounded : (ℂ → ℂ) → Type₀
ComplexLocallyBounded =
  ComplexLocallyBoundedWithin wholeℂ


localBoundRadiusLeft :
  ∀ h radiusF radiusG →
  modulus h <ᵣ rat (fst (min₊ radiusF radiusG)) →
  modulus h <ᵣ rat (fst radiusF)
localBoundRadiusLeft h radiusF radiusG |h|<minimum =
  isTrans<≤ᵣ _ _ _ |h|<minimum
    (≤ℚ→≤ᵣ _ _
      (ℚ.min≤ (fst radiusF) (fst radiusG)))


localBoundRadiusRight :
  ∀ h radiusF radiusG →
  modulus h <ᵣ rat (fst (min₊ radiusF radiusG)) →
  modulus h <ᵣ rat (fst radiusG)
localBoundRadiusRight h radiusF radiusG |h|<minimum =
  isTrans<≤ᵣ _ _ _ |h|<minimum
    (≤ℚ→≤ᵣ _ _
      (ℚ.min≤' (fst radiusF) (fst radiusG)))


complexLocalBoundWithinAt-restrict :
  ∀ {P Q f z} →
  Q ⊆ P →
  ComplexLocalBoundWithinAt P f z →
  ComplexLocalBoundWithinAt Q f z
complexLocalBoundWithinAt-restrict
  {P} {Q} {f} {z} Q⊆P (radius , bound , estimate) =
  radius , bound ,
  λ h z+h∈Q |h|<radius →
    estimate h (Q⊆P (z +ℂ h) z+h∈Q) |h|<radius


complexLocalBoundWithinAt-shrink :
  ∀ {P f z} →
  (localBound : ComplexLocalBoundWithinAt P f z) →
  (radius : ℚ₊) →
  radius ≤₊ fst localBound →
  ComplexLocalBoundWithinAt P f z
complexLocalBoundWithinAt-shrink
  {P} {f} {z}
  (oldRadius , bound , estimate) radius radius≤oldRadius =
  radius , bound ,
  λ h z+h∈P |h|<radius →
    estimate h z+h∈P
      (isTrans<≤ᵣ _ _ _
        |h|<radius
        (≤ℚ→≤ᵣ _ _ radius≤oldRadius))


complexLocalBoundWithinAt-cong :
  ∀ {P f g z} →
  ((w : ℂ) → w ∈ P → f w ≡ g w) →
  ComplexLocalBoundWithinAt P f z →
  ComplexLocalBoundWithinAt P g z
complexLocalBoundWithinAt-cong
  {P} {f} {g} {z} f≡g (radius , bound , estimate) =
  radius , bound ,
  λ h z+h∈P |h|<radius →
    subst
      (_≤ᵣ rat (fst bound))
      (cong modulus (f≡g (z +ℂ h) z+h∈P))
      (estimate h z+h∈P |h|<radius)


opaque
  complexLocalBoundWithinAt-centerBound :
    ∀ {P f z} →
    z ∈ P →
    ComplexLocalBoundWithinAt P f z →
    ComplexScalarBound (f z)
  complexLocalBoundWithinAt-centerBound
    {P} {f} {z} z∈P (radius , bound , estimate) =
    bound ,
    subst
      (_≤ᵣ rat (fst bound))
      (cong modulus (cong f (+ℂIdR z)))
      (estimate 0ℂ
        (subst (_∈ P) (sym (+ℂIdR z)) z∈P)
        (subst (_<ᵣ rat (fst radius))
          (sym modulus0)
          (<ℚ→<ᵣ 0 (fst radius) (snd radius))))


complexLocalBoundWithinAt-constant :
  ∀ P c z →
  ComplexScalarBound c →
  ComplexLocalBoundWithinAt P (λ _ → c) z
complexLocalBoundWithinAt-constant
  P c z (bound , |c|≤bound) =
  1 , bound ,
  λ _ _ _ → |c|≤bound


complexLocalBoundWithinAt-identityWithRadius :
  ∀ P z radius →
  ComplexScalarBound z →
  ComplexLocalBoundWithinAt P (λ w → w) z
complexLocalBoundWithinAt-identityWithRadius
  P z radius (bound , |z|≤bound) =
  radius , bound +₊ radius ,
  λ h _ |h|<radius →
    isTrans≤≡ᵣ _ _ _
      (isTrans≤ᵣ _ _ _
        (modulus-triangle z h)
        (≤ᵣMonotone+ᵣ _ _ _ _
          |z|≤bound
          (<ᵣWeaken≤ᵣ _ _ |h|<radius)))
      (+ᵣ-rat (fst bound) (fst radius))


complexLocalBoundWithinAt-identity :
  ∀ P z →
  ComplexScalarBound z →
  ComplexLocalBoundWithinAt P (λ w → w) z
complexLocalBoundWithinAt-identity P z =
  complexLocalBoundWithinAt-identityWithRadius P z 1


complexLocalBoundWithinAt-neg :
  ∀ {P f z} →
  ComplexLocalBoundWithinAt P f z →
  ComplexLocalBoundWithinAt P (λ w → -ℂ f w) z
complexLocalBoundWithinAt-neg
  {P} {f} {z} (radius , bound , estimate) =
  radius , bound ,
  λ h z+h∈P |h|<radius →
    isTrans≡≤ᵣ _ _ _
      (modulus-neg (f (z +ℂ h)))
      (estimate h z+h∈P |h|<radius)


complexLocalBoundWithinAt-add :
  ∀ {P f g z} →
  ComplexLocalBoundWithinAt P f z →
  ComplexLocalBoundWithinAt P g z →
  ComplexLocalBoundWithinAt P (λ w → f w +ℂ g w) z
complexLocalBoundWithinAt-add
  {P} {f} {g} {z}
  (radiusF , boundF , estimateF)
  (radiusG , boundG , estimateG) =
  min₊ radiusF radiusG , boundF +₊ boundG ,
  λ h z+h∈P |h|<minimum →
    isTrans≤≡ᵣ _ _ _
      (isTrans≤ᵣ _ _ _
        (modulus-triangle
          (f (z +ℂ h)) (g (z +ℂ h)))
        (≤ᵣMonotone+ᵣ _ _ _ _
          (estimateF h z+h∈P
            (localBoundRadiusLeft
              h radiusF radiusG |h|<minimum))
          (estimateG h z+h∈P
            (localBoundRadiusRight
              h radiusF radiusG |h|<minimum))))
      (+ᵣ-rat (fst boundF) (fst boundG))


complexLocalBoundWithinAt-mul :
  ∀ {P f g z} →
  ComplexLocalBoundWithinAt P f z →
  ComplexLocalBoundWithinAt P g z →
  ComplexLocalBoundWithinAt P (λ w → f w ·ℂ g w) z
complexLocalBoundWithinAt-mul
  {P} {f} {g} {z}
  (radiusF , boundF , estimateF)
  (radiusG , boundG , estimateG) =
  min₊ radiusF radiusG , boundF ·₊ boundG ,
  λ h z+h∈P |h|<minimum →
    isTrans≡≤ᵣ _ _ _
      (modulus-mul
        (f (z +ℂ h)) (g (z +ℂ h)))
      (isTrans≤≡ᵣ _ _ _
        (≤ᵣ₊Monotone·ᵣ
          (modulus (f (z +ℂ h))) (rat (fst boundF))
          (modulus (g (z +ℂ h))) (rat (fst boundG))
          (<ᵣWeaken≤ᵣ _ _
            (snd (ℚ₊→ℝ₊ boundF)))
          (modulusNonNeg (g (z +ℂ h)))
          (estimateF h z+h∈P
            (localBoundRadiusLeft
              h radiusF radiusG |h|<minimum))
          (estimateG h z+h∈P
            (localBoundRadiusRight
              h radiusF radiusG |h|<minimum)))
        (sym
          (rat·ᵣrat
            (fst boundF) (fst boundG))))


complexLocalBoundWithinAt-scale :
  ∀ {P f z} c →
  ComplexScalarBound c →
  ComplexLocalBoundWithinAt P f z →
  ComplexLocalBoundWithinAt P (λ w → c ·ℂ f w) z
complexLocalBoundWithinAt-scale
  {P} {f} {z} c (boundC , |c|≤boundC)
  (radius , boundF , estimateF) =
  radius , boundC ·₊ boundF ,
  λ h z+h∈P |h|<radius →
    isTrans≡≤ᵣ _ _ _
      (modulus-mul c (f (z +ℂ h)))
      (isTrans≤≡ᵣ _ _ _
        (≤ᵣ₊Monotone·ᵣ
          (modulus c) (rat (fst boundC))
          (modulus (f (z +ℂ h))) (rat (fst boundF))
          (<ᵣWeaken≤ᵣ _ _
            (snd (ℚ₊→ℝ₊ boundC)))
          (modulusNonNeg (f (z +ℂ h)))
          |c|≤boundC
          (estimateF h z+h∈P |h|<radius))
        (sym
          (rat·ᵣrat
            (fst boundC) (fst boundF))))


complexLocallyBoundedWithin-constant :
  ∀ P c →
  ComplexScalarBound c →
  ComplexLocallyBoundedWithin P (λ _ → c)
complexLocallyBoundedWithin-constant P c bound z _ =
  complexLocalBoundWithinAt-constant P c z bound
