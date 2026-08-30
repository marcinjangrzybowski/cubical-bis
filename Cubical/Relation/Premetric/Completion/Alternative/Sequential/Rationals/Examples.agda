module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.Examples where

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
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.CauchyContinuous
  as CauchyContinuousDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.LocallyUniformlyContinuous
  as LocallyUniformDefinition

module S = SequentialDefinition ℚPremetricSpace
module SP = SequentialPropertiesDefinition ℚPremetricSpace
module C = CauchyContinuousDefinition
module Local = LocallyUniformDefinition

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

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing

private
  module Pℚ = PremetricStr (ℚPremetricSpace .snd)
  module Pℚ² = PremetricStr (ℚ²PremetricSpace .snd)
  module STheory = PremetricTheory SP.ℭ̂ₛPremetricSpace
  module PPℚ² = PremetricStr (PP.ℭ̂ₛPremetricSpace .snd)
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


-- The sequential completion of the ordinary rational premetric is the real
-- type used in this example.

ℝₛ : Type₀
ℝₛ = S.ℭ̂ₛ

rat : ℚ → ℝₛ
rat = S.ι


squareℚ : ℚ → ℚ
squareℚ x = x · x

private
  signedSquareAbs≡square : ∀ x →
    signedSquareℚ (abs x) ≡ squareℚ x
  signedSquareAbs≡square x =
      signedSquareℚ≡·abs (abs x)
    ∙ cong (abs x ·_) (0≤→abs≡id (abs x) (0≤abs x))
    ∙ abs·abs x x
    ∙ 0≤→abs≡id (x · x) (0≤² x)

  absAbsDistance≤ : ∀ x y →
    abs (abs x - abs y) ≤ℚ abs (x - y)
  absAbsDistance≤ x y =
    ℚ.absFrom≤×≤ distance difference lowerBound upperBound
    where
    distance = abs (x - y)
    difference = abs x - abs y

    upperBound : difference ≤ℚ distance
    upperBound = abs-abs≤abs- x y

    swapped : abs y - abs x ≤ℚ distance
    swapped = subst ((abs y - abs x) ≤ℚ_)
      (abs-Comm y x) (abs-abs≤abs- y x)

    lowerBound : - distance ≤ℚ difference
    lowerBound = subst (- distance ≤ℚ_)
      (ℚ.-[x-y]≡y-x (abs y) (abs x))
      (ℚ.minus-≤ (abs y - abs x) distance swapped)

  abs-pres≈ : ∀ x y ε →
    x Pℚ.≈[ ε ] y → abs x Pℚ.≈[ ε ] abs y
  abs-pres≈ x y ε x≈y =
    ℚ.isTrans≤< _ _ _ (absAbsDistance≤ x y) x≈y

  abs-bounded : ∀ (x : ℚ) (B : ℚ₊) →
    abs x ≤ℚ fst B → abs (abs x) ≤ℚ fst B
  abs-bounded x B =
    subst (_≤ℚ fst B)
      (sym (0≤→abs≡id (abs x) (0≤abs x)))


-- Squaring is locally uniformly continuous because it is signed squaring
-- after absolute value.  Absolute value is non-expanding and preserves each
-- centered rational ball.

squareℚ-locallyUniformlyContinuous :
  Local.IsLocallyUniformlyContinuous squareℚ
squareℚ-locallyUniformlyContinuous B =
  PT.map makeLocal
    (Local.signedSquareℚ-locallyUniformlyContinuous B)
  where
  makeLocal :
    (Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
      Local.IsUniformlyContinuousOnBallWith signedSquareℚ B μ) →
    Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
      Local.IsUniformlyContinuousOnBallWith squareℚ B μ
  makeLocal (μ , local) = μ , squareLocal
    where
    squareLocal : Local.IsUniformlyContinuousOnBallWith squareℚ B μ
    squareLocal .Local.IsUniformlyContinuousOnBallWith.pres≈
      x y ε absx≤B absy≤B x≈y =
      subst2 (λ u v → u Pℚ.≈[ ε ] v)
        (signedSquareAbs≡square x)
        (signedSquareAbs≡square y)
        (local .Local.IsUniformlyContinuousOnBallWith.pres≈
          (abs x) (abs y) ε
          (abs-bounded x B absx≤B)
          (abs-bounded y B absy≤B)
          (abs-pres≈ x y (μ ε) x≈y))


-- The local-continuity development supplies the graph-Cauchy hypothesis.
-- We only transfer that proof object; the extension below is the independent
-- rational construction from Rationals.CauchyContinuous.

private
  genericSquareCauchyContinuous :
    Local.CC.C.IsCauchyContinuous (S.ι ∘ squareℚ)
  genericSquareCauchyContinuous =
    Local.CC.completionCenteredContinuous→cauchyContinuous
      (Local.locallyUniformlyContinuous→completionCenteredContinuous
        squareℚ squareℚ-locallyUniformlyContinuous)

squareℚ-isCauchyContinuous : C.IsCauchyContinuousBase squareℚ
squareℚ-isCauchyContinuous = C.cauchyContinuous
  (genericSquareCauchyContinuous
    .Local.CC.C.IsCauchyContinuous.presCauchyGraph)

squareℚ-mapsRationalCauchySequences :
  C.MapsRationalCauchySequences squareℚ
squareℚ-mapsRationalCauchySequences =
  C.isCauchyContinuousBase→mapsRationalCauchySequences
    squareℚ-isCauchyContinuous


squareℝ : ℝₛ → ℝₛ
squareℝ =
  C.liftCauchyContinuousBase squareℚ squareℚ-isCauchyContinuous

squareℝ-rat : ∀ q → squareℝ (rat q) ≡ rat (squareℚ q)
squareℝ-rat =
  C.liftCauchyContinuousBase-ι squareℚ squareℚ-isCauchyContinuous

squareℝ-presCauchy : C.MapsCompletionCauchySequences squareℝ
squareℝ-presCauchy =
  C.liftCauchyContinuousBase-presCauchy
    squareℚ squareℚ-isCauchyContinuous


-- Multiplication is naturally a map out of the product premetric space.
-- Its completion is a joint representation of two real arguments.

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
    a · b - c · d ≡
      (a - c) · b + c · (b - d)
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
  ProductCC.IsCompletionCenteredContinuous (S.ι ∘ multiplyℚ)
multiplyℚ-completionCentered
  .ProductCC.IsCompletionCenteredContinuous.at x =
  PT.rec squash₁ withAnchor (PP.∃approx x 1)
  where
  withAnchor :
    (Σ[ a ∈ (ℚ × ℚ) ] (P.ι a P.∼̂ₛ[ 1 ] x)) →
    ∃[ ν ∈ (ℚ₊ → ℚ₊) ]
      ProductCC.IsCompletionContinuousAtWith (S.ι ∘ multiplyℚ) x ν
  withAnchor (a , anchor) = ∣ ν , centered ∣₁
    where
    B₁ = Local.anchorBound (fst a)
    B₂ = Local.anchorBound (snd a)
    L = B₂ +₊ B₁

    ν : ℚ₊ → ℚ₊
    ν ε = min₊ (ε ₊／₊ L) 1 /2₊

    centered :
      ProductCC.IsCompletionContinuousAtWith (S.ι ∘ multiplyℚ) x ν
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

ℝ²ₛ : Type₀
ℝ²ₛ = P.ℭ̂ₛ

multiplyℝ² : ℝ²ₛ → ℝₛ
multiplyℝ² =
  ProductCC.liftCompletionCenteredContinuous
    (S.ι ∘ multiplyℚ) multiplyℚ-completionCentered

multiplyℝ²-rat : ∀ q →
  multiplyℝ² (P.ι q) ≡ rat (multiplyℚ q)
multiplyℝ²-rat (p , q) = refl


-- The product-completion isomorphism turns the jointly lifted map into an
-- ordinary curried operation on two sequential real numbers.

multiplyℝ : ℝₛ → ℝₛ → ℝₛ
multiplyℝ =
  curry (multiplyℝ² ∘ SequentialProduct.productToCompletion)

multiplyℝ-rat : ∀ p q →
  multiplyℝ (rat p) (rat q) ≡ rat (p · q)
multiplyℝ-rat p q = refl

multiplyℝ-lim-rat : ∀ x xs q →
  multiplyℝ (S.lim x ∣ xs ∣₁) (rat q) ≡ S.lim (λ n → multiplyℝ (x _) (rat q)) _
multiplyℝ-lim-rat x xs q  = refl


multiplyℝ-rat-lim : ∀ q x xs →
  multiplyℝ (rat q) (S.lim x ∣ xs ∣₁)  ≡ S.lim (λ n → multiplyℝ (rat q) (x _)) _
multiplyℝ-rat-lim x xs q  = refl


multiplyℝ²-lim-lim-refl : ∀ x xs y ys →
  multiplyℝ (S.lim x ∣ xs ∣₁) (S.lim y ys ) ≡
   S.lim (λ n → multiplyℝ (x _) (S.lim y ys)) _ 
multiplyℝ²-lim-lim-refl x xs y ys = refl



multiplyℝ²-lim-lim : ∀ x xs y ys s' →
  multiplyℝ (S.lim x xs) (S.lim y ys) ≡
   S.lim (λ n → multiplyℝ (x n) (y n)) s'
multiplyℝ²-lim-lim x xs y ys s' =
  cong fst (STheory.isPropLimitSeq image
    (multiplyℝ (S.lim x xs) (S.lim y ys) , image-limit)
    (S.lim image s' , SP.lim-isLimitSeq image s'))
  where
  pairSeq : ℕ.ℕ → ℝₛ × ℝₛ
  pairSeq n = x n , y n


-- private
  multiplyℝ²ᶜ : C[ PP.ℭ̂ₛPremetricSpace , SP.ℭ̂ₛPremetricSpace ]
  multiplyℝ²ᶜ = multiplyℝ² ,
    ProductCC.liftCompletionCenteredContinuous-isContinuous
      (S.ι ∘ multiplyℚ) multiplyℚ-completionCentered

  pairLimit : ℝₛ × ℝₛ
  pairLimit = S.lim x xs , S.lim y ys

  pair-limit : PremetricTheory.isLimitSeq
    (PremetricProduct SP.ℭ̂ₛPremetricSpace SP.ℭ̂ₛPremetricSpace)
    pairSeq pairLimit
  pair-limit = pairPresIsLimitSeq
    {M = SP.ℭ̂ₛPremetricSpace} {N = SP.ℭ̂ₛPremetricSpace} x y
    (S.lim x xs) (S.lim y ys)
    (SP.lim-isLimitSeq x xs) (SP.lim-isLimitSeq y ys)

  joint-limit : PremetricTheory.isLimitSeq PP.ℭ̂ₛPremetricSpace
    (SequentialProduct.productToCompletion ∘ pairSeq)
    (SequentialProduct.productToCompletion pairLimit)
  joint-limit =
    SequentialProduct.productToCompletion-presIsLimitSeq
      pairSeq pairLimit pair-limit

  image : ℕ.ℕ → ℝₛ
  image n = multiplyℝ (x n) (y n)

  image-limit : STheory.isLimitSeq image
    (multiplyℝ (S.lim x xs) (S.lim y ys))
  image-limit = C→seqContinuous multiplyℝ²ᶜ
    (SequentialProduct.productToCompletion ∘ pairSeq)
    (SequentialProduct.productToCompletion pairLimit)
    joint-limit



-- -- -- multiplyℝ²-presCauchy :
-- -- --   ProductC.MapsCompletionCauchySequences multiplyℝ²
-- -- -- multiplyℝ²-presCauchy =
-- -- --   ProductC.liftCauchyContinuousBase-presCauchy
-- -- --     multiplyℚ multiplyℚ-isCauchyContinuous
