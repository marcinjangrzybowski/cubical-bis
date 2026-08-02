module Cubical.HITs.CauchyRealsP.Algebra.Lattice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Extensionality

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Completion.Properties.Lift

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

private
  rationalMaxNE₁ : ∀ y →
    IsNonExpanding
      (snd ℚPremetricSpace)
      (λ x → rat (ℚ.max x y))
      (snd ℝPremetricSpace)
  rationalMaxNE₁ y .IsNonExpanding.pres≈ x x' ε x≈x' =
    rat-rat _ _ ε
      (subst (ℚ._< ⟨ ε ⟩₊)
        (cong abs
          (cong₂ ℚ._-_
            (ℚ.maxComm y x)
            (ℚ.maxComm y x')))
        (ℚ.isTrans≤< _ _ _
          (ℚ.maxDist y x' x) x≈x'))

  rationalMaxNE₂ : ∀ x →
    IsNonExpanding
      (snd ℚPremetricSpace)
      (λ y → rat (ℚ.max x y))
      (snd ℝPremetricSpace)
  rationalMaxNE₂ x .IsNonExpanding.pres≈ y y' ε y≈y' =
    rat-rat _ _ ε
      (ℚ.isTrans≤< _ _ _
        (ℚ.maxDist x y' y) y≈y')

  rationalMaxLip₁ : ∀ y →
    IsLipschitzWith
      (snd ℚPremetricSpace)
      (λ x → rat (ℚ.max x y))
      (snd ℝPremetricSpace) 1
  rationalMaxLip₁ y =
    isNonExpanding→isLipschitzWith1
      (snd ℚPremetricSpace) _
      (snd ℝPremetricSpace) (rationalMaxNE₁ y)

  rationalMaxLip₂ : ∀ x →
    IsLipschitzWith
      (snd ℚPremetricSpace)
      (λ y → rat (ℚ.max x y))
      (snd ℝPremetricSpace) 1
  rationalMaxLip₂ x =
    isNonExpanding→isLipschitzWith1
      (snd ℚPremetricSpace) _
      (snd ℝPremetricSpace) (rationalMaxNE₂ x)

  maxExtension =
    liftLipschitzBinaryWith
      ℚPremetricSpace ℚPremetricSpace ℝPremetricSpace
      isCompleteℝ 1 1
      (λ x y → rat (ℚ.max x y))
      rationalMaxLip₁ rationalMaxLip₂

maxℝ : ℝ → ℝ → ℝ
maxℝ = fst maxExtension

max-rat : ∀ x y → maxℝ (rat x) (rat y) ≡ rat (ℚ.max x y)
max-rat x y =
  funExt⁻
    (funExt⁻
      (liftBinary∘ι∘ι
        ℚPremetricSpace ℚPremetricSpace ℝPremetricSpace
        isCompleteℝ 1 1
        (λ p q → rat (ℚ.max p q))
        rationalMaxLip₁ rationalMaxLip₂)
      x)
    y

maxIsNonExpanding₂ : ∀ x →
  IsNonExpanding
    (snd ℝPremetricSpace) (maxℝ x) (snd ℝPremetricSpace)
maxIsNonExpanding₂ x =
  isLipschitzWith1→isNonExpanding
    (snd ℝPremetricSpace) (maxℝ x)
    (snd ℝPremetricSpace) (fst (snd maxExtension) x)

maxPres∼₂ : ∀ x y y' ε
  → y ∼[ ε ] y'
  → maxℝ x y ∼[ ε ] maxℝ x y'
maxPres∼₂ x y y' ε =
  IsNonExpanding.pres≈ (maxIsNonExpanding₂ x) y y' ε

maxPres∼₁ : ∀ x x' y ε
  → x ∼[ ε ] x'
  → maxℝ x y ∼[ ε ] maxℝ x' y
maxPres∼₁ x x' y ε x∼x' =
  ≈→→pointwise ℝ ℝPremetricSpace
    (maxℝ x) (maxℝ x') ε
    (IsNonExpanding.pres≈ maxNE→ x x' ε x∼x')
    y
  where
  maxNE→ :
    IsNonExpanding
      (snd ℝPremetricSpace)
      maxℝ
      (snd (→PremetricSpace ℝ ℝPremetricSpace))
  maxNE→ =
    isLipschitzWith1→isNonExpanding
      (snd ℝPremetricSpace) maxℝ
      (snd (→PremetricSpace ℝ ℝPremetricSpace))
      (snd (snd maxExtension))

maxIsNonExpanding₁ : ∀ y →
  IsNonExpanding
    (snd ℝPremetricSpace) (λ x → maxℝ x y) (snd ℝPremetricSpace)
maxIsNonExpanding₁ y
  .IsNonExpanding.pres≈ x x' ε =
    maxPres∼₁ x x' y ε

maxPres∼ : ∀ x x' y y' ε δ
  → x ∼[ ε ] x'
  → y ∼[ δ ] y'
  → maxℝ x y ∼[ ε +₊ δ ] maxℝ x' y'
maxPres∼ x x' y y' ε δ x∼x' y∼y' =
  triangle∼ (maxℝ x y) (maxℝ x' y) (maxℝ x' y') ε δ
    (maxPres∼₁ x x' y ε x∼x')
    (maxPres∼₂ x' y y' δ y∼y')

module _
  {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A)
  where
  private
    module Source = PremetricStr source

  maxOfContinuousIsContinuous :
    (f g : A → ℝ) →
    isContinuous source f (snd ℝPremetricSpace) →
    isContinuous source g (snd ℝPremetricSpace) →
    isContinuous source
      (λ x → maxℝ (f x) (g x))
      (snd ℝPremetricSpace)
  maxOfContinuousIsContinuous f g f-cont g-cont x
    .IsContinuousAt.pres≈ ε =
      PT.map2
        (λ (δf , f-near) (δg , g-near) →
          min₊ δf δg
          , λ y x≈y →
              subst∼
                (maxℝ (f x) (g x))
                (maxℝ (f y) (g y))
                {ε = (ε /2₊) +₊ (ε /2₊)}
                {ε' = ε}
                (1/2∈ℚ./2+/2≡id (fst ε))
                (maxPres∼
                  (f x) (f y) (g x) (g y)
                  (ε /2₊) (ε /2₊)
                  (f-near y
                    (Source.isMonotone≈≤
                      x y (min₊ δf δg) δf
                      (min₊≤L δf δg) x≈y))
                  (g-near y
                    (Source.isMonotone≈≤
                      x y (min₊ δf δg) δg
                      (min₊≤R δf δg) x≈y))))
        (f-cont x .IsContinuousAt.pres≈ (ε /2₊))
        (g-cont x .IsContinuousAt.pres≈ (ε /2₊))

maxComm : ∀ x y → maxℝ x y ≡ maxℝ y x
maxComm =
  nonExpandingExtensionality₂
    maxℝ (flip maxℝ)
    maxIsNonExpanding₁
    maxIsNonExpanding₂
    (λ y → maxIsNonExpanding₂ y)
    (λ x → maxIsNonExpanding₁ x)
    λ p q →
      max-rat p q
      ∙ cong rat (ℚ.maxComm p q)
      ∙ sym (max-rat q p)

private
  composeIsNonExpanding :
    (f g : ℝ → ℝ)
    → IsNonExpanding (snd ℝPremetricSpace) f (snd ℝPremetricSpace)
    → IsNonExpanding (snd ℝPremetricSpace) g (snd ℝPremetricSpace)
    → IsNonExpanding (snd ℝPremetricSpace) (f ∘ g)
        (snd ℝPremetricSpace)
  composeIsNonExpanding f g f-ne g-ne
    .IsNonExpanding.pres≈ x y ε x∼y =
      IsNonExpanding.pres≈ f-ne (g x) (g y) ε
        (IsNonExpanding.pres≈ g-ne x y ε x∼y)

  identityIsNonExpanding :
    IsNonExpanding
      (snd ℝPremetricSpace) (idfun ℝ) (snd ℝPremetricSpace)
  identityIsNonExpanding
    .IsNonExpanding.pres≈ _ _ _ x∼y = x∼y

  diagonalMaxIsLipschitzWith2 :
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ x → maxℝ x x)
      (snd ℝPremetricSpace) 2
  diagonalMaxIsLipschitzWith2
    .IsLipschitzWith.pres≈ x y ε x∼y =
      subst∼ (maxℝ x x) (maxℝ y y)
        {ε = ε +₊ ε} {ε' = 2 ·₊ ε}
        ℚ!
        (maxPres∼ x y x y ε ε x∼y x∼y)

maxAssoc : ∀ x y z →
  maxℝ x (maxℝ y z) ≡ maxℝ (maxℝ x y) z
maxAssoc =
  nonExpandingExtensionality₃
    (λ x y z → maxℝ x (maxℝ y z))
    (λ x y z → maxℝ (maxℝ x y) z)
    (λ y z → maxIsNonExpanding₁ (maxℝ y z))
    (λ x z →
      composeIsNonExpanding
        (maxℝ x) (λ y → maxℝ y z)
        (maxIsNonExpanding₂ x) (maxIsNonExpanding₁ z))
    (λ x y →
      composeIsNonExpanding
        (maxℝ x) (maxℝ y)
        (maxIsNonExpanding₂ x) (maxIsNonExpanding₂ y))
    (λ y z →
      composeIsNonExpanding
        (λ u → maxℝ u z) (λ x → maxℝ x y)
        (maxIsNonExpanding₁ z) (maxIsNonExpanding₁ y))
    (λ x z →
      composeIsNonExpanding
        (λ u → maxℝ u z) (maxℝ x)
        (maxIsNonExpanding₁ z) (maxIsNonExpanding₂ x))
    (λ x y → maxIsNonExpanding₂ (maxℝ x y))
    λ p q r →
      cong (maxℝ (rat p)) (max-rat q r)
      ∙ max-rat p (ℚ.max q r)
      ∙ cong rat (ℚ.maxAssoc p q r)
      ∙ sym (max-rat (ℚ.max p q) r)
      ∙ cong (λ u → maxℝ u (rat r)) (sym (max-rat p q))

maxIdem : ∀ x → maxℝ x x ≡ x
maxIdem =
  funExt⁻
    (lipschitzExtensionality ℝPremetricSpace
      (λ x → maxℝ x x) (idfun ℝ)
      ∣ 2 , diagonalMaxIsLipschitzWith2 ∣₁
      (isNonExpanding→isLipschitz
        (snd ℝPremetricSpace) (idfun ℝ)
        (snd ℝPremetricSpace) identityIsNonExpanding)
      λ q → max-rat q q ∙ cong rat (ℚ.maxIdem q))

minℝ : ℝ → ℝ → ℝ
minℝ x y = - maxℝ (- x) (- y)

min-rat : ∀ x y → minℝ (rat x) (rat y) ≡ rat (ℚ.min x y)
min-rat x y =
  cong -_ (cong₂ maxℝ (neg-rat x) (neg-rat y))
  ∙ cong -_ (max-rat (ℚ.- x) (ℚ.- y))
  ∙ neg-rat (ℚ.max (ℚ.- x) (ℚ.- y))
  ∙ cong rat
      (cong ℚ.-_ (ℚ.maxNeg≡negMin x y)
      ∙ ℚ.-Invol (ℚ.min x y))

minPres∼₁ : ∀ x x' y ε
  → x ∼[ ε ] x'
  → minℝ x y ∼[ ε ] minℝ x' y
minPres∼₁ x x' y ε x∼x' =
  negPres∼ _ _ ε
    (maxPres∼₁ (- x) (- x') (- y) ε
      (negPres∼ x x' ε x∼x'))

minPres∼₂ : ∀ x y y' ε
  → y ∼[ ε ] y'
  → minℝ x y ∼[ ε ] minℝ x y'
minPres∼₂ x y y' ε y∼y' =
  negPres∼ _ _ ε
    (maxPres∼₂ (- x) (- y) (- y') ε
      (negPres∼ y y' ε y∼y'))

minIsNonExpanding₁ : ∀ y →
  IsNonExpanding
    (snd ℝPremetricSpace) (λ x → minℝ x y) (snd ℝPremetricSpace)
minIsNonExpanding₁ y
  .IsNonExpanding.pres≈ x x' ε =
    minPres∼₁ x x' y ε

minIsNonExpanding₂ : ∀ x →
  IsNonExpanding
    (snd ℝPremetricSpace) (minℝ x) (snd ℝPremetricSpace)
minIsNonExpanding₂ x
  .IsNonExpanding.pres≈ y y' ε =
    minPres∼₂ x y y' ε

minComm : ∀ x y → minℝ x y ≡ minℝ y x
minComm =
  nonExpandingExtensionality₂
    minℝ (flip minℝ)
    minIsNonExpanding₁
    minIsNonExpanding₂
    (λ y → minIsNonExpanding₂ y)
    (λ x → minIsNonExpanding₁ x)
    λ p q →
      min-rat p q
      ∙ cong rat (ℚ.minComm p q)
      ∙ sym (min-rat q p)

minAssoc : ∀ x y z →
  minℝ x (minℝ y z) ≡ minℝ (minℝ x y) z
minAssoc =
  nonExpandingExtensionality₃
    (λ x y z → minℝ x (minℝ y z))
    (λ x y z → minℝ (minℝ x y) z)
    (λ y z → minIsNonExpanding₁ (minℝ y z))
    (λ x z →
      composeIsNonExpanding
        (minℝ x) (λ y → minℝ y z)
        (minIsNonExpanding₂ x) (minIsNonExpanding₁ z))
    (λ x y →
      composeIsNonExpanding
        (minℝ x) (minℝ y)
        (minIsNonExpanding₂ x) (minIsNonExpanding₂ y))
    (λ y z →
      composeIsNonExpanding
        (λ u → minℝ u z) (λ x → minℝ x y)
        (minIsNonExpanding₁ z) (minIsNonExpanding₁ y))
    (λ x z →
      composeIsNonExpanding
        (λ u → minℝ u z) (minℝ x)
        (minIsNonExpanding₁ z) (minIsNonExpanding₂ x))
    (λ x y → minIsNonExpanding₂ (minℝ x y))
    λ p q r →
      cong (minℝ (rat p)) (min-rat q r)
      ∙ min-rat p (ℚ.min q r)
      ∙ cong rat (ℚ.minAssoc p q r)
      ∙ sym (min-rat (ℚ.min p q) r)
      ∙ cong (λ u → minℝ u (rat r)) (sym (min-rat p q))

minIdem : ∀ x → minℝ x x ≡ x
minIdem x =
  cong -_ (maxIdem (- x))
  ∙ negInvol x
