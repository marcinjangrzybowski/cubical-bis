module Cubical.Analysis.Real.Algebra.Multiplication.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
import Cubical.Data.Nat as ℕ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Analysis.Real.Base

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals
open import Cubical.Relation.Premetric.Instances.Product

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.Regular
  as RegularComparisonDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Product
  as SequentialProductDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CauchyContinuous
  as GenericCauchyContinuousDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CompletionCentered
  as CompletionCenteredDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.LocallyUniformlyContinuous
  as LocallyUniformDefinition

ℚ²PremetricSpace : PremetricSpace ℓ-zero ℓ-zero
ℚ²PremetricSpace = PremetricProduct ℚPremetricSpace ℚPremetricSpace

module P = SequentialDefinition ℚ²PremetricSpace
module PP = SequentialPropertiesDefinition ℚ²PremetricSpace
module ProductComparison = RegularComparisonDefinition ℚ²PremetricSpace
module ProductC = GenericCauchyContinuousDefinition
  ℚ²PremetricSpace ℚPremetricSpace
module ProductCC = CompletionCenteredDefinition
  ℚ²PremetricSpace ℚPremetricSpace
module SequentialProduct = SequentialProductDefinition
  ℚPremetricSpace ℚPremetricSpace
module Local = LocallyUniformDefinition

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open CategoryStructures
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing

private
  module Pℚ = PremetricStr (ℚPremetricSpace .snd)
  module Pℚ² = PremetricStr (ℚ²PremetricSpace .snd)
  module STheory = PremetricTheory ℝPremetricSpace
  module PPℚ² = PremetricStr (PP.ℭ̂ₛPremetricSpace .snd)
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


multiplyℚ : ℚ × ℚ → ℚ
multiplyℚ q = fst q · snd q

private
  telescopingDifference : ∀ x y z →
    (x - y) + (y - z) ≡ x - z
  telescopingDifference x y z =
    (x + (- y)) + (y + (- z))
      ≡⟨ ℚ.+Assoc (x + (- y)) y (- z) ⟩
    ((x + (- y)) + y) + (- z)
      ≡⟨ cong (_+ (- z)) (sym (ℚ.+Assoc x (- y) y)) ⟩
    (x + ((- y) + y)) + (- z)
      ≡⟨ cong (λ w → (x + w) + (- z)) (ℚ.+InvL y) ⟩
    (x + 0) + (- z)
      ≡⟨ cong (_+ (- z)) (ℚ.+IdR x) ⟩
    x - z ∎

  multiplyDifference : ∀ a b c d →
    a · b - c · d ≡ (a - c) · b + c · (b - d)
  multiplyDifference a b c d =
    sym (telescopingDifference (a · b) (c · b) (c · d))
    ∙ cong₂ _+_
        (sym (ℚRing.·DistL- a c b))
        (sym (ℚRing.·DistR- c b d))

  multiplyBounded : ∀ B₁ B₂ q r ε →
    abs (snd q) ≤ℚ fst B₂ →
    abs (fst r) ≤ℚ fst B₁ →
    q Pℚ².≈[ ε ] r →
    multiplyℚ q Pℚ.≈[ (B₂ +₊ B₁) ·₊ ε ] multiplyℚ r
  multiplyBounded B₁ B₂ q r ε absq₂≤B₂ absr₁≤B₁ q≈r =
    subst (abs (multiplyℚ q - multiplyℚ r) <ℚ_)
      factor (isTrans≤< _ _ _ estimate strict)
    where
    estimate :
      abs (multiplyℚ q - multiplyℚ r) ≤ℚ
        abs (fst q - fst r) · fst B₂ +
        fst B₁ · abs (snd q - snd r)
    estimate = isTrans≤ _ _ _ triangleStep boundedStep
      where
      sumOfAbsoluteValues =
        abs ((fst q - fst r) · snd q) +
        abs (fst r · (snd q - snd r))

      sumOfProducts =
        abs (fst q - fst r) · abs (snd q) +
        abs (fst r) · abs (snd q - snd r)

      triangleStep :
        abs (multiplyℚ q - multiplyℚ r) ≤ℚ sumOfProducts
      triangleStep =
        subst (abs (multiplyℚ q - multiplyℚ r) ≤ℚ_)
          (cong₂ _+_
            (sym (abs·abs (fst q - fst r) (snd q)))
            (sym (abs·abs (fst r) (snd q - snd r))))
          (subst (_≤ℚ sumOfAbsoluteValues)
            (sym (cong abs
              (multiplyDifference (fst q) (snd q) (fst r) (snd r))))
            (triangularInequality
              ((fst q - fst r) · snd q)
              (fst r · (snd q - snd r))))

      boundedStep : sumOfProducts ≤ℚ
        abs (fst q - fst r) · fst B₂ +
        fst B₁ · abs (snd q - snd r)
      boundedStep = +Mono≤ _ _ _ _
        (·MonoL≤ (abs (snd q)) (fst B₂) (abs (fst q - fst r))
          (0≤abs (fst q - fst r)) absq₂≤B₂)
        (·MonoR≤ (abs (fst r)) (fst B₁) (abs (snd q - snd r))
          (0≤abs (snd q - snd r)) absr₁≤B₁)

    strict :
      abs (fst q - fst r) · fst B₂ +
        fst B₁ · abs (snd q - snd r) <ℚ
      fst ε · fst B₂ + fst B₁ · fst ε
    strict = +Mono< _ _ _ _
      (·MonoR< (abs (fst q - fst r)) (fst ε) (fst B₂)
        (snd B₂) (fst q≈r))
      (·MonoL< (abs (snd q - snd r)) (fst ε) (fst B₁)
        (snd B₁) (snd q≈r))

    factor :
      fst ε · fst B₂ + fst B₁ · fst ε ≡
      fst ((B₂ +₊ B₁) ·₊ ε)
    factor = cong₂ _+_ (ℚ.·Comm (fst ε) (fst B₂)) refl
      ∙ sym (ℚ.·DistR+ (fst B₂) (fst B₁) (fst ε))

  productApproximationBounded : ∀ a x q δ →
    P.ι a P.∼̂ₛ[ 1 ] x →
    δ <₊ 1 →
    P.ι q P.∼̂ₛ[ δ ] x →
    (abs (fst q) ≤ℚ fst (Local.anchorBound (fst a))) ×
    (abs (snd q) ≤ℚ fst (Local.anchorBound (snd a)))
  productApproximationBounded a x q δ ιa∼x δ<1 ιq∼x =
    Local.closeToAnchor-bounded (fst a) (fst q) (fst q≈a) ,
    Local.closeToAnchor-bounded (snd a) (snd q) (snd q≈a)
    where
    q≈a : q Pℚ².≈[ 1 +₊ 1 ] a
    q≈a = ProductComparison.ι-reflects∼ q a (1 +₊ 1)
      (P.isMonotone∼̂ₛ< (P.ι q) (P.ι a) (δ +₊ 1) (1 +₊ 1)
        (+MonoR< (fst δ) 1 1 δ<1)
        (P.tri∼ (P.ι q) x (P.ι a) δ 1
          ιq∼x (P.sym∼ (P.ι a) x 1 ιa∼x)))


multiplyℚ-completionCentered :
  ProductCC.IsCompletionCenteredContinuous (rat ∘ multiplyℚ)
multiplyℚ-completionCentered
  .ProductCC.IsCompletionCenteredContinuous.at x =
  PT.rec squash₁ withAnchor (PP.∃approx x 1)
  where
  withAnchor :
    (Σ[ a ∈ (ℚ × ℚ) ] (P.ι a P.∼̂ₛ[ 1 ] x)) →
    ∃[ ν ∈ (ℚ₊ → ℚ₊) ]
      ProductCC.IsCompletionContinuousAtWith (rat ∘ multiplyℚ) x ν
  withAnchor (a , anchor) = ∣ ν , centered ∣₁
    where
    B₁ = Local.anchorBound (fst a)
    B₂ = Local.anchorBound (snd a)
    L = B₂ +₊ B₁

    ν : ℚ₊ → ℚ₊
    ν ε = min₊ (ε ₊／₊ L) 1 /2₊

    centered :
      ProductCC.IsCompletionContinuousAtWith (rat ∘ multiplyℚ) x ν
    centered .ProductCC.IsCompletionContinuousAtWith.pres∼
      q r ε ιq∼x ιr∼x =
      S.ι-ι (multiplyℚ q) (multiplyℚ r) ε
        (Pℚ.subst≈ (multiplyℚ q) (multiplyℚ r)
          {ε = L ·₊ (ε ₊／₊ L)} {ε' = ε} (·／ L ε)
          (multiplyBounded B₁ B₂ q r (ε ₊／₊ L)
            (snd q-bounded) (fst r-bounded) q≈r))
      where
      q-bounded = productApproximationBounded a x q (ν ε) anchor
        (min/2₊<R (ε ₊／₊ L) 1) ιq∼x

      r-bounded = productApproximationBounded a x r (ν ε) anchor
        (min/2₊<R (ε ₊／₊ L) 1) ιr∼x

      radius≤ : (ν ε +₊ ν ε) ≤₊ (ε ₊／₊ L)
      radius≤ = subst (_≤ℚ fst (ε ₊／₊ L))
        (sym (/2+/2≡id (fst (min₊ (ε ₊／₊ L) 1))))
        (min₊≤L (ε ₊／₊ L) 1)

      q≈r : q Pℚ².≈[ ε ₊／₊ L ] r
      q≈r = ProductComparison.ι-reflects∼ q r (ε ₊／₊ L)
        (PPℚ².isMonotone≈≤ (P.ι q) (P.ι r)
          (ν ε +₊ ν ε) (ε ₊／₊ L) radius≤
          (P.tri∼ (P.ι q) x (P.ι r) (ν ε) (ν ε)
            ιq∼x (P.sym∼ (P.ι r) x (ν ε) ιr∼x)))


multiplyℚ-isCauchyContinuous :
  ProductC.IsCauchyContinuousBase multiplyℚ
multiplyℚ-isCauchyContinuous =
  ProductCC.completionCenteredContinuous→cauchyContinuous
    multiplyℚ-completionCentered

ℝ² : Type₀
ℝ² = P.ℭ̂ₛ

multiplyℝ² : ℝ² → ℝ
multiplyℝ² =
  ProductCC.liftCompletionCenteredContinuous
    (rat ∘ multiplyℚ) multiplyℚ-completionCentered

multiplyℝ²-rat : ∀ q →
  multiplyℝ² (P.ι q) ≡ rat (multiplyℚ q)
multiplyℝ²-rat (p , q) = refl

multiplyℝ : ℝ → ℝ → ℝ
multiplyℝ =
  curry (multiplyℝ² ∘ SequentialProduct.productToCompletion)

multiplyℝ-rat : ∀ p q →
  multiplyℝ (rat p) (rat q) ≡ rat (p · q)
multiplyℝ-rat p q = refl


multiplyℝ²ᶜ : C[ PP.ℭ̂ₛPremetricSpace , ℝPremetricSpace ]
multiplyℝ²ᶜ = multiplyℝ² ,
  ProductCC.liftCompletionCenteredContinuous-isContinuous
    (rat ∘ multiplyℚ) multiplyℚ-completionCentered

multiplyOnProductᶜ : C[
  PremetricProduct ℝPremetricSpace ℝPremetricSpace , ℝPremetricSpace ]
multiplyOnProductᶜ =
  multiplyℝ²ᶜ ∘C L→C SequentialProduct.productToCompletionᴸ

multiplyℝ-isContinuous₁ : ∀ y → isContinuous
  (ℝPremetricSpace .snd) (flip multiplyℝ y) (ℝPremetricSpace .snd)
multiplyℝ-isContinuous₁ y = snd
  (multiplyOnProductᶜ ∘C
    rightInsertionC ℝPremetricSpace ℝPremetricSpace y)

multiplyℝ-isContinuous₂ : ∀ x → isContinuous
  (ℝPremetricSpace .snd) (multiplyℝ x) (ℝPremetricSpace .snd)
multiplyℝ-isContinuous₂ x = snd
  (multiplyOnProductᶜ ∘C
    leftInsertionC ℝPremetricSpace ℝPremetricSpace x)


multiplyℝ-lim-lim : ∀ x xs y ys s' →
  multiplyℝ (lim x xs) (lim y ys) ≡
  lim (λ n → multiplyℝ (x n) (y n)) s'
multiplyℝ-lim-lim x xs y ys s' =
  cong fst (STheory.isPropLimitSeq image
    (multiplyℝ (lim x xs) (lim y ys) , image-limit)
    (lim image s' , lim-isLimitSeq image s'))
  where
  pairSeq : ℕ.ℕ → ℝ × ℝ
  pairSeq n = x n , y n

  pairLimit : ℝ × ℝ
  pairLimit = lim x xs , lim y ys

  pair-limit : PremetricTheory.isLimitSeq
    (PremetricProduct ℝPremetricSpace ℝPremetricSpace)
    pairSeq pairLimit
  pair-limit = pairPresIsLimitSeq
    {M = ℝPremetricSpace} {N = ℝPremetricSpace} x y
    (lim x xs) (lim y ys)
    (lim-isLimitSeq x xs) (lim-isLimitSeq y ys)

  joint-limit : PremetricTheory.isLimitSeq PP.ℭ̂ₛPremetricSpace
    (SequentialProduct.productToCompletion ∘ pairSeq)
    (SequentialProduct.productToCompletion pairLimit)
  joint-limit =
    SequentialProduct.productToCompletion-presIsLimitSeq
      pairSeq pairLimit pair-limit

  image : ℕ.ℕ → ℝ
  image n = multiplyℝ (x n) (y n)

  image-limit : STheory.isLimitSeq image
    (multiplyℝ (lim x xs) (lim y ys))
  image-limit = C→seqContinuous multiplyℝ²ᶜ
    (SequentialProduct.productToCompletion ∘ pairSeq)
    (SequentialProduct.productToCompletion pairLimit)
    joint-limit
