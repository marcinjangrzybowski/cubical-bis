module Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Bounded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Extensionality
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Clamp

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.Relation.Premetric.Completion.Properties.Lift

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

private
  module ℚOrder = OrderedCommRingTheory ℚOrderedCommRing

  clampLower : ℚ₊ → ℚ
  clampLower B = ℚ.- fst B

  clampUpper : ℚ₊ → ℚ
  clampUpper = fst

  rationalClampLower≤Upper : ∀ B → clampLower B ℚ.≤ clampUpper B
  rationalClampLower≤Upper B =
    ℚ.isTrans≤
      (clampLower B) 0 (clampUpper B)
      (-ℚ₊≤0 B) (ℚ.0≤ℚ₊ B)

clampAt : ℚ₊ → ℚ → ℚ
clampAt B = ℚ.clamp (clampLower B) (clampUpper B)

clampAtAbs≤ : ∀ B q → abs (clampAt B q) ℚ.≤ fst B
clampAtAbs≤ B q =
  ℚ.absFrom≤×≤
    (fst B) (clampAt B q)
    (ℚ.≤clamp
      (clampLower B) (clampUpper B) q
      (rationalClampLower≤Upper B))
    (ℚ.clamp≤ (clampLower B) (clampUpper B) q)

boundedMulℚ : ℚ₊ → ℚ → ℚ → ℚ
boundedMulℚ B q r = clampAt B q ℚ.· clampAt B r

private
  boundedMulLip₁ : ∀ B r →
    IsLipschitzWith
      (snd ℚPremetricSpace)
      (λ q → rat (boundedMulℚ B q r))
      (snd ℝPremetricSpace) B
  boundedMulLip₁ B r
    .IsLipschitzWith.pres≈ q q' ε q∼q' =
      rat-rat _ _ (B ·₊ ε)
        (subst (ℚ._< fst (B ·₊ ε))
          (sym outputDistancePath)
          productDistanceBound)
    where
    cq cq' cr : ℚ
    cq = clampAt B q
    cq' = clampAt B q'
    cr = clampAt B r

    clampDistance≤ :
      abs (cq ℚ.- cq') ℚ.≤ abs (q ℚ.- q')
    clampDistance≤ =
      ℚ.clampDist (clampLower B) (clampUpper B) q' q

    firstProduct≤ :
      abs (cq ℚ.- cq') ℚ.· abs cr
        ℚ.≤ abs (q ℚ.- q') ℚ.· abs cr
    firstProduct≤ =
      ℚ.≤-·o
        (abs (cq ℚ.- cq')) (abs (q ℚ.- q')) (abs cr)
        (ℚOrder.0≤abs cr)
        clampDistance≤

    secondProduct≤ :
      abs (q ℚ.- q') ℚ.· abs cr
        ℚ.≤ fst B ℚ.· abs (q ℚ.- q')
    secondProduct≤ =
      subst
        (ℚ._≤ (fst B ℚ.· abs (q ℚ.- q')))
        (ℚ.·Comm (abs cr) (abs (q ℚ.- q')))
        (ℚ.≤-·o
          (abs cr) (fst B) (abs (q ℚ.- q'))
          (ℚOrder.0≤abs (q ℚ.- q'))
          (clampAtAbs≤ B r))

    productDistanceBound :
      abs (cq ℚ.- cq') ℚ.· abs cr
        ℚ.< fst B ℚ.· fst ε
    productDistanceBound =
      ℚ.isTrans≤<
        (abs (cq ℚ.- cq') ℚ.· abs cr)
        (fst B ℚ.· abs (q ℚ.- q'))
        (fst B ℚ.· fst ε)
        (ℚ.isTrans≤
          (abs (cq ℚ.- cq') ℚ.· abs cr)
          (abs (q ℚ.- q') ℚ.· abs cr)
          (fst B ℚ.· abs (q ℚ.- q'))
          firstProduct≤ secondProduct≤)
        (ℚ.<-o·
          (abs (q ℚ.- q')) (fst ε) (fst B)
          (snd B) q∼q')

    outputDistancePath :
      abs (boundedMulℚ B q r ℚ.- boundedMulℚ B q' r) ≡
      abs (cq ℚ.- cq') ℚ.· abs cr
    outputDistancePath =
      cong
        {x = boundedMulℚ B q r ℚ.- boundedMulℚ B q' r}
        {y = (cq ℚ.- cq') ℚ.· cr}
        abs ℚ!
      ∙ sym (ℚ.abs·abs (cq ℚ.- cq') cr)

  boundedMulLip₂ : ∀ B q →
    IsLipschitzWith
      (snd ℚPremetricSpace)
      (λ r → rat (boundedMulℚ B q r))
      (snd ℝPremetricSpace) B
  boundedMulLip₂ B q =
    subst
      (λ f →
        IsLipschitzWith
          (snd ℚPremetricSpace) f
          (snd ℝPremetricSpace) B)
      (funExt λ r →
        cong rat (ℚ.·Comm (clampAt B r) (clampAt B q)))
      (boundedMulLip₁ B q)

  boundedMulExtension : ∀ B →
    Σ[ f ∈ (ℝ → ℝ → ℝ) ]
      ((∀ x →
        IsLipschitzWith
          (snd ℝPremetricSpace) (f x)
          (snd ℝPremetricSpace) B)
      × IsLipschitzWith
          (snd ℝPremetricSpace) f
          (snd (→PremetricSpace ℝ ℝPremetricSpace)) B)
  boundedMulExtension B =
    liftLipschitzBinaryWith
      ℚPremetricSpace ℚPremetricSpace ℝPremetricSpace
      isCompleteℝ B B
      (λ q r → rat (boundedMulℚ B q r))
      (boundedMulLip₁ B)
      (boundedMulLip₂ B)

boundedMulℝ : ℚ₊ → ℝ → ℝ → ℝ
boundedMulℝ B = fst (boundedMulExtension B)

boundedMul-rat : ∀ B q r →
  boundedMulℝ B (rat q) (rat r) ≡ rat (boundedMulℚ B q r)
boundedMul-rat B q r =
  funExt⁻
    (funExt⁻
      (liftBinary∘ι∘ι
        ℚPremetricSpace ℚPremetricSpace ℝPremetricSpace
        isCompleteℝ B B
        (λ q r → rat (boundedMulℚ B q r))
        (boundedMulLip₁ B)
        (boundedMulLip₂ B))
      q)
    r

boundedMulIsLipschitz₂ : ∀ B x →
  IsLipschitzWith
    (snd ℝPremetricSpace) (boundedMulℝ B x)
    (snd ℝPremetricSpace) B
boundedMulIsLipschitz₂ B = fst (snd (boundedMulExtension B))

boundedMulIsLipschitz₁ :
  ∀ B →
  IsLipschitzWith
    (snd ℝPremetricSpace) (boundedMulℝ B)
    (snd (→PremetricSpace ℝ ℝPremetricSpace)) B
boundedMulIsLipschitz₁ B = snd (snd (boundedMulExtension B))

boundedMulIsLipschitz₁At : ∀ B y →
  IsLipschitzWith
    (snd ℝPremetricSpace) (λ x → boundedMulℝ B x y)
    (snd ℝPremetricSpace) B
boundedMulIsLipschitz₁At B y
  .IsLipschitzWith.pres≈ x x' ε x∼x' =
    ≈→→pointwise ℝ ℝPremetricSpace
      (boundedMulℝ B x) (boundedMulℝ B x') (B ·₊ ε)
      (IsLipschitzWith.pres≈
        (boundedMulIsLipschitz₁ B) x x' ε x∼x')
      y

boundedMulComm : ∀ B x y →
  boundedMulℝ B x y ≡ boundedMulℝ B y x
boundedMulComm B =
  lipschitzExtensionality₂
    (boundedMulℝ B) (flip (boundedMulℝ B))
    (λ y → ∣ B , boundedMulIsLipschitz₁At B y ∣₁)
    (λ x → ∣ B , boundedMulIsLipschitz₂ B x ∣₁)
    (λ y → ∣ B , boundedMulIsLipschitz₂ B y ∣₁)
    (λ x → ∣ B , boundedMulIsLipschitz₁At B x ∣₁)
    λ p q →
      boundedMul-rat B p q
      ∙ cong rat (ℚ.·Comm (clampAt B p) (clampAt B q))
      ∙ sym (boundedMul-rat B q p)

clampAtIdem : ∀ B q →
  clampAt B (clampAt B q) ≡ clampAt B q
clampAtIdem B q =
  ℚ.inClamps
    (clampLower B) (clampUpper B) (clampAt B q)
    (ℚ.≤clamp
      (clampLower B) (clampUpper B) q
      (rationalClampLower≤Upper B))
    (ℚ.clamp≤ (clampLower B) (clampUpper B) q)

clampAtLarger : ∀ B C →
  fst B ℚ.≤ fst C →
  ∀ q → clampAt C (clampAt B q) ≡ clampAt B q
clampAtLarger B C B≤C q =
  ℚ.inClamps
    (clampLower C) (clampUpper C) (clampAt B q)
    (ℚ.isTrans≤
      (clampLower C) (clampLower B) (clampAt B q)
      (ℚ.minus-≤ (fst B) (fst C) B≤C)
      (ℚ.≤clamp
        (clampLower B) (clampUpper B) q
        (rationalClampLower≤Upper B)))
    (ℚ.isTrans≤
      (clampAt B q) (clampUpper B) (clampUpper C)
      (ℚ.clamp≤ (clampLower B) (clampUpper B) q)
      B≤C)

boundedMul-rat-within : ∀ B q r →
  clampLower B ℚ.≤ q → q ℚ.≤ clampUpper B →
  clampLower B ℚ.≤ r → r ℚ.≤ clampUpper B →
  boundedMulℝ B (rat q) (rat r) ≡ rat (q ℚ.· r)
boundedMul-rat-within B q r lower≤q q≤upper lower≤r r≤upper =
  boundedMul-rat B q r
  ∙ cong rat
      (cong₂ ℚ._·_
        (ℚ.inClamps
          (clampLower B) (clampUpper B) q lower≤q q≤upper)
        (ℚ.inClamps
          (clampLower B) (clampUpper B) r lower≤r r≤upper))

private
  boundedMulAfterClampLip₁ : ∀ A B y →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ x → boundedMulℝ A (clampℝ B x) (clampℝ B y))
      (snd ℝPremetricSpace) A
  boundedMulAfterClampLip₁ A B y
    .IsLipschitzWith.pres≈ x x' ε x∼x' =
      IsLipschitzWith.pres≈
        (boundedMulIsLipschitz₁At A (clampℝ B y))
        (clampℝ B x) (clampℝ B x') ε
        (clampPres∼ B x x' ε x∼x')

  boundedMulAfterClampLip₂ : ∀ A B x →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ y → boundedMulℝ A (clampℝ B x) (clampℝ B y))
      (snd ℝPremetricSpace) A
  boundedMulAfterClampLip₂ A B x
    .IsLipschitzWith.pres≈ y y' ε y∼y' =
      IsLipschitzWith.pres≈
        (boundedMulIsLipschitz₂ A (clampℝ B x))
        (clampℝ B y) (clampℝ B y') ε
        (clampPres∼ B y y' ε y∼y')

boundedMulClamp : ∀ B x y →
  boundedMulℝ B (clampℝ B x) (clampℝ B y) ≡
  boundedMulℝ B x y
boundedMulClamp B =
  lipschitzExtensionality₂
    (λ x y → boundedMulℝ B (clampℝ B x) (clampℝ B y))
    (boundedMulℝ B)
    (λ y → ∣ B , boundedMulAfterClampLip₁ B B y ∣₁)
    (λ x → ∣ B , boundedMulAfterClampLip₂ B B x ∣₁)
    (λ y → ∣ B , boundedMulIsLipschitz₁At B y ∣₁)
    (λ x → ∣ B , boundedMulIsLipschitz₂ B x ∣₁)
    λ p q →
      cong₂ (boundedMulℝ B)
        (clamp-rat B p) (clamp-rat B q)
      ∙ boundedMul-rat B (clampAt B p) (clampAt B q)
      ∙ cong rat
          (cong₂ ℚ._·_
            (clampAtIdem B p)
            (clampAtIdem B q))
      ∙ sym (boundedMul-rat B p q)

boundedMulContained : ∀ B C →
  fst B ℚ.≤ fst C →
  ∀ x y →
  boundedMulℝ C (clampℝ B x) (clampℝ B y) ≡
  boundedMulℝ B x y
boundedMulContained B C B≤C =
  lipschitzExtensionality₂
    (λ x y → boundedMulℝ C (clampℝ B x) (clampℝ B y))
    (boundedMulℝ B)
    (λ y → ∣ C , boundedMulAfterClampLip₁ C B y ∣₁)
    (λ x → ∣ C , boundedMulAfterClampLip₂ C B x ∣₁)
    (λ y → ∣ B , boundedMulIsLipschitz₁At B y ∣₁)
    (λ x → ∣ B , boundedMulIsLipschitz₂ B x ∣₁)
    λ p q →
      cong₂ (boundedMulℝ C)
        (clamp-rat B p) (clamp-rat B q)
      ∙ boundedMul-rat C (clampAt B p) (clampAt B q)
      ∙ cong rat
          (cong₂ ℚ._·_
            (clampAtLarger B C B≤C p)
            (clampAtLarger B C B≤C q))
      ∙ sym (boundedMul-rat B p q)

boundedMulAgreeWithin : ∀ B C →
  fst B ℚ.≤ fst C →
  ∀ x y →
  rat (clampLower B) ≤ℝ x → x ≤ℝ rat (clampUpper B) →
  rat (clampLower B) ≤ℝ y → y ≤ℝ rat (clampUpper B) →
  boundedMulℝ C x y ≡ boundedMulℝ B x y
boundedMulAgreeWithin B C B≤C x y lower≤x x≤upper lower≤y y≤upper =
  sym
    (cong₂ (boundedMulℝ C)
      (clampFixpoint B x lower≤x x≤upper)
      (clampFixpoint B y lower≤y y≤upper))
  ∙ boundedMulContained B C B≤C x y

boundedMulAgreeWithinAbs : ∀ B C →
  fst B ℚ.≤ fst C →
  ∀ x y →
  absℝ x ≤ℝ rat (fst B) →
  absℝ y ≤ℝ rat (fst B) →
  boundedMulℝ C x y ≡ boundedMulℝ B x y
boundedMulAgreeWithinAbs B C B≤C x y absx≤B absy≤B =
  boundedMulAgreeWithin B C B≤C x y
    (fst (absBound→clampBounds B x absx≤B))
    (snd (absBound→clampBounds B x absx≤B))
    (fst (absBound→clampBounds B y absy≤B))
    (snd (absBound→clampBounds B y absy≤B))
