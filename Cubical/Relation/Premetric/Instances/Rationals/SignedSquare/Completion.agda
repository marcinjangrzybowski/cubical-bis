module Cubical.Relation.Premetric.Instances.Rationals.SignedSquare.Completion where

-- The signed-square embedding is isometric by construction and has dense
-- rational image.  Hence it extends to an isometric equivalence of completions.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Nat as ℕ using (ℕ; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Bisection as Bisection
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.Rationals
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Completion.Properties.Lift

open import Cubical.Categories.Category.Base using (CatIso; isIso)

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing
open 1/2∈ℚ
open PositiveRationals
open PositiveHalvesℚ

private
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)

  negatedAbsDifference : ∀ x y → - (abs y - abs x) ≡ abs x - abs y
  negatedAbsDifference x y = ℚ!

  signedSquareDifference : ∀ x y →
    x · abs x - y · abs y ≡ (x - y) · abs x + y · (abs x - abs y)
  signedSquareDifference x y = ℚ!

  boundedDifferenceSum : ∀ B x y →
    abs (x - y) · B + B · abs (x - y) ≡ (B + B) · abs (x - y)
  boundedDifferenceSum B x y = ℚ!

  abs-abs-difference≤ : ∀ x y → abs (abs x - abs y) ≤ abs (x - y)
  abs-abs-difference≤ x y = ℚ.absFrom≤×≤ d q lowerBound upperBound
    where
    d = abs (x - y)
    q = abs x - abs y

    upperBound : q ≤ d
    upperBound = abs-abs≤abs- x y

    swapped : abs y - abs x ≤ d
    swapped = subst ((abs y - abs x) ≤_) (abs-Comm y x) (abs-abs≤abs- y x)

    lowerBound : - d ≤ q
    lowerBound = subst (- d ≤_) (negatedAbsDifference x y)
      (ℚ.minus-≤ (abs y - abs x) d swapped)

signedSquareℚ-bounded : ∀ (B : ℚ₊) x y
  → abs x ≤ fst B
  → abs y ≤ fst B
  → abs (signedSquareℚ x - signedSquareℚ y)
      ≤ fst (B +₊ B) · abs (x - y)
signedSquareℚ-bounded B x y absx≤B absy≤B = begin≤
  abs (signedSquareℚ x - signedSquareℚ y)
    ≡→≤⟨ cong abs (cong₂ _-_ (signedSquareℚ≡·abs x) (signedSquareℚ≡·abs y)) ⟩
  abs (x · abs x - y · abs y)
    ≡→≤⟨ cong abs (signedSquareDifference x y) ⟩
  abs ((x - y) · abs x + y · (abs x - abs y))
    ≤⟨ triangularInequality ((x - y) · abs x) (y · (abs x - abs y)) ⟩
  abs ((x - y) · abs x) + abs (y · (abs x - abs y))
    ≡→≤⟨ cong₂ _+_
      (sym (abs·abs (x - y) (abs x))
        ∙ cong (abs (x - y) ·_) (0≤→abs≡id (abs x) (0≤abs x)))
      (sym (abs·abs y (abs x - abs y))) ⟩
  abs (x - y) · abs x + abs y · abs (abs x - abs y)
    ≤⟨ +Mono≤ _ _ _ _
      (·MonoL≤ (abs x) (fst B) (abs (x - y)) (0≤abs (x - y)) absx≤B)
      (·Mono≤ (abs y) (fst B) (abs (abs x - abs y)) (abs (x - y))
        (<-≤-weaken 0 (fst B) (snd B)) (0≤abs (abs x - abs y))
        absy≤B (abs-abs-difference≤ x y)) ⟩
  abs (x - y) · fst B + fst B · abs (x - y)
    ≡→≤⟨ boundedDifferenceSum (fst B) x y ⟩
  fst (B +₊ B) · abs (x - y) ◾

private
  signedSquareBound : ℚ → ℚ₊
  signedSquareBound y = maxWithPos 1 (abs y)

  module SignedSquareApproximation (y : ℚ) where
    B : ℚ₊
    B = signedSquareBound y

    L : ℚ₊
    L = B +₊ B

    B≤B² : fst B ≤ fst B · fst B
    B≤B² = subst (_≤ fst B · fst B) (·IdR (fst B))
      (·MonoL≤ 1 (fst B) (fst B) (<-≤-weaken 0 (fst B) (snd B))
        (ℚ.≤max 1 (abs y)))

    y≤B² : y ≤ fst B · fst B
    y≤B² = ℚ.isTrans≤ _ (abs y) _ (≤abs y)
      (ℚ.isTrans≤ _ (fst B) _ (ℚ.≤max' 1 (abs y)) B≤B²)

    -B²≤y : - (fst B · fst B) ≤ y
    -B²≤y = ℚ.isTrans≤ _ (- abs y) _
      (-Flip≤ (abs y) (fst B · fst B)
        (ℚ.isTrans≤ _ (fst B) _ (ℚ.≤max' 1 (abs y)) B≤B²))
      (subst (- abs y ≤_) (ℚRing.-Idempotent y)
        (-Flip≤ (- y) (abs y) (-≤abs y)))

    negativeValue : signedSquareℚ (- fst B) ≡ - (fst B · fst B)
    negativeValue = signedSquareℚ≡·abs (- fst B)
      ∙ cong ((- fst B) ·_) (≤0→abs≡- (- fst B) (-ℚ₊≤0 B))
      ∙ negativeProduct
      where
      negativeProduct : (- fst B) · (- (- fst B)) ≡ - (fst B · fst B)
      negativeProduct = ℚ!

    positiveValue : signedSquareℚ (fst B) ≡ fst B · fst B
    positiveValue = signedSquareℚ≡·abs (fst B)
      ∙ cong (fst B ·_) (0≤→abs≡id (fst B) (<-≤-weaken 0 (fst B) (snd B)))

    brackets : (signedSquareℚ (- fst B) ≤ y) × (y ≤ signedSquareℚ (fst B))
    fst brackets = subst (_≤ y) (sym negativeValue) -B²≤y
    snd brackets = subst (y ≤_) (sym positiveValue) y≤B²

    -B<B : - fst B < fst B
    -B<B = ℚ.isTrans< _ 0 _ (-ℚ₊<0 B) (snd B)

    module Bisect = ℚIncrFunBisectFamily
      (- fst B) (fst B) -B<B signedSquareℚ

    index : ℚ₊ → ℕ
    index ε = suc (fst (Bisect.widthEventually< y (ε ₊／₊ L)))

    approximation : ℚ₊ → ℚ
    approximation ε = Bisect.bs y (index ε)

    private
      index-large : ∀ ε → fst (Bisect.widthEventually< y (ε ₊／₊ L)) ℕ.< index ε
      index-large ε = ℕ.≤-refl

      width< : ∀ ε → Bisect.width y (index ε) < fst (ε ₊／₊ L)
      width< ε = snd (Bisect.widthEventually< y (ε ₊／₊ L))
        (index ε) (index-large ε)

      lower-valid : ∀ ε → signedSquareℚ (approximation ε) ≤ y
      lower-valid ε = Bisect.bs-lower-valid y (fst brackets) (index ε)

      upper-valid : ∀ ε → y ≤ signedSquareℚ (Bisect.bs↑ y (index ε))
      upper-valid ε = Bisect.bs↑-upper-valid y (snd brackets) (index ε)

      lower-abs≤B : ∀ ε → abs (approximation ε) ≤ fst B
      lower-abs≤B ε = ℚ.absFrom≤×≤ (fst B) (approximation ε)
        (Bisect.a≤bs y (index ε)) (Bisect.bs≤b y (index ε))

      upper-abs≤B : ∀ ε → abs (Bisect.bs↑ y (index ε)) ≤ fst B
      upper-abs≤B ε = ℚ.absFrom≤×≤ (fst B) (Bisect.bs↑ y (index ε))
        (Bisect.a≤bs↑ y (index ε)) (Bisect.bs↑≤b y (index ε))

      image-width≤ : ∀ ε →
        signedSquareℚ (Bisect.bs↑ y (index ε)) - signedSquareℚ (approximation ε)
          ≤ fst L · Bisect.width y (index ε)
      image-width≤ ε = begin≤
        signedSquareℚ (Bisect.bs↑ y (index ε)) - signedSquareℚ (approximation ε)
          ≤⟨ ≤abs (signedSquareℚ (Bisect.bs↑ y (index ε)) - signedSquareℚ (approximation ε)) ⟩
        abs (signedSquareℚ (Bisect.bs↑ y (index ε)) - signedSquareℚ (approximation ε))
          ≤⟨ signedSquareℚ-bounded B
            (Bisect.bs↑ y (index ε)) (approximation ε)
            (upper-abs≤B ε) (lower-abs≤B ε) ⟩
        fst L · abs (Bisect.bs↑ y (index ε) - approximation ε)
          ≡→≤⟨ cong (fst L ·_)
            (0≤→abs≡id
              (Bisect.bs↑ y (index ε) - approximation ε)
              (Bisect.widthNonNeg y (index ε))) ⟩
        fst L · Bisect.width y (index ε) ◾

    close : ∀ ε → abs (signedSquareℚ (approximation ε) - y) < fst ε
    close ε = subst (_< fst ε)
      (sym (abs-Comm (signedSquareℚ (approximation ε)) y
        ∙ 0≤→abs≡id (y - signedSquareℚ (approximation ε))
          (ℚ.-≤ _ _ (lower-valid ε))))
      (ℚ.isTrans≤< _ (fst L · Bisect.width y (index ε)) _
        (ℚ.isTrans≤ _
          (signedSquareℚ (Bisect.bs↑ y (index ε)) - signedSquareℚ (approximation ε)) _
          (ℚ.≤-+o y (signedSquareℚ (Bisect.bs↑ y (index ε)))
            (- signedSquareℚ (approximation ε)) (upper-valid ε))
          (image-width≤ ε))
        (subst (fst L · Bisect.width y (index ε) <_)
          (·／ L ε)
          (·MonoL< _ _ (fst L) (snd L) (width< ε))))

opaque
  signedSquareℚ-dense : ∀ (y : ℚ) (ε : ℚ₊)
    → Σ[ x ∈ ℚ ] abs (signedSquareℚ x - y) < fst ε
  signedSquareℚ-dense y ε =
    SignedSquareApproximation.approximation y ε , SignedSquareApproximation.close y ε

module SignedCompletion where
  open import Cubical.Relation.Premetric.Completion.Base
    ℚSignedSquarePremetricSpace public
  open import Cubical.Relation.Premetric.Completion.Properties.Closeness
    ℚSignedSquarePremetricSpace public

module OrdinaryCompletion where
  open import Cubical.Relation.Premetric.Completion.Base
    ℚPremetricSpace public
  open import Cubical.Relation.Premetric.Completion.Properties.Closeness
    ℚPremetricSpace public

private
  module SignedTheory = PremetricTheory SignedCompletion.ℭPremetricSpace
  module OrdinaryTheory = PremetricTheory OrdinaryCompletion.ℭPremetricSpace
  module SignedBase = PremetricStr (snd SignedCompletion.ℭPremetricSpace)
  module OrdinaryBase = PremetricStr (snd ℚPremetricSpace)

signedRootApproximation : ℚ → ℚ₊ → ℚ
signedRootApproximation y ε = fst (signedSquareℚ-dense y ε)

signedRootApproximation-close : ∀ y ε →
  abs (signedSquareℚ (signedRootApproximation y ε) - y) < fst ε
signedRootApproximation-close y ε = snd (signedSquareℚ-dense y ε)

signedRootSequence : ℚ → ℚ₊ → SignedCompletion.ℭ
signedRootSequence y ε = SignedCompletion.ι (signedRootApproximation y ε)

signedRootCauchy : ∀ y ε δ →
  signedRootSequence y ε SignedCompletion.∼[ ε +₊ δ ] signedRootSequence y δ
signedRootCauchy y ε δ = SignedCompletion.ι-ι _ _ (ε +₊ δ) $ ℚ.recompute< $ begin<
  abs (signedSquareℚ (signedRootApproximation y ε)
       - signedSquareℚ (signedRootApproximation y δ))
    ≤⟨ triangularInequality-
      (signedSquareℚ (signedRootApproximation y ε))
      (signedSquareℚ (signedRootApproximation y δ)) y ⟩
  abs (signedSquareℚ (signedRootApproximation y ε) - y)
    + abs (y - signedSquareℚ (signedRootApproximation y δ))
    <⟨ +Mono< _ _ _ _
      (signedRootApproximation-close y ε)
      (subst (_< fst δ)
        (sym (abs-Comm y (signedSquareℚ (signedRootApproximation y δ))))
        (signedRootApproximation-close y δ)) ⟩
  fst (ε +₊ δ) ◾

approximateSignedRoot : ℚ → SignedCompletion.ℭ
approximateSignedRoot y =
  SignedCompletion.lim (signedRootSequence y) (signedRootCauchy y)

approximateSignedRoot-isLimit : ∀ y →
  SignedTheory.isLimit (signedRootSequence y) (approximateSignedRoot y)
approximateSignedRoot-isLimit y =
  SignedCompletion.isLimitLim (signedRootSequence y) (signedRootCauchy y)

private
  signedRootApproximation-pres≈ : ∀ y z κ η
    → abs (y - z) < fst κ
    → signedRootSequence y η
        SignedCompletion.∼[ η +₊ (κ +₊ η) ] signedRootSequence z η
  signedRootApproximation-pres≈ y z κ η y≈z =
    SignedCompletion.ι-ι _ _ (η +₊ (κ +₊ η)) $ ℚ.recompute< $ begin<
      abs (signedSquareℚ (signedRootApproximation y η)
           - signedSquareℚ (signedRootApproximation z η))
        ≤⟨ triangularInequality-
          (signedSquareℚ (signedRootApproximation y η))
          (signedSquareℚ (signedRootApproximation z η)) y ⟩
      abs (signedSquareℚ (signedRootApproximation y η) - y)
        + abs (y - signedSquareℚ (signedRootApproximation z η))
        ≤⟨ +Mono≤
          (abs (signedSquareℚ (signedRootApproximation y η) - y))
          (abs (signedSquareℚ (signedRootApproximation y η) - y))
          (abs (y - signedSquareℚ (signedRootApproximation z η)))
          (abs (y - z) + abs (z - signedSquareℚ (signedRootApproximation z η)))
          (ℚ.isRefl≤ (abs (signedSquareℚ (signedRootApproximation y η) - y)))
          (triangularInequality- y
            (signedSquareℚ (signedRootApproximation z η)) z) ⟩
      abs (signedSquareℚ (signedRootApproximation y η) - y)
        + (abs (y - z)
        + abs (z - signedSquareℚ (signedRootApproximation z η)))
        <⟨ +Mono<
          (abs (signedSquareℚ (signedRootApproximation y η) - y)) (fst η)
          (abs (y - z) + abs (z - signedSquareℚ (signedRootApproximation z η)))
          (fst κ + fst η)
          (signedRootApproximation-close y η)
          (+Mono< (abs (y - z)) (fst κ)
            (abs (z - signedSquareℚ (signedRootApproximation z η))) (fst η) y≈z
            (subst (_< fst η)
              (sym (abs-Comm z
                (signedSquareℚ (signedRootApproximation z η))))
              (signedRootApproximation-close z η))) ⟩
      fst (η +₊ (κ +₊ η)) ◾

approximateSignedRootⁿ : NE[ ℚPremetricSpace , SignedCompletion.ℭPremetricSpace ]
fst approximateSignedRootⁿ = approximateSignedRoot
IsNonExpanding.pres≈ (snd approximateSignedRootⁿ) y z ε y≈z =
  PT.rec
    (SignedBase.isProp≈ (approximateSignedRoot y) (approximateSignedRoot z) ε)
    step
    (OrdinaryBase.isRounded≈ y z ε y≈z)
  where
  step : Σ[ κ ∈ ℚ₊ ] (κ <₊ ε) × (abs (y - z) < fst κ)
    → approximateSignedRoot y SignedCompletion.∼[ ε ] approximateSignedRoot z
  step (κ , κ<ε , y≈κz) =
    SignedBase.isRounded≈⁻ (approximateSignedRoot y) (approximateSignedRoot z) ε
      ∣ radius
      , radius<ε
      , SignedTheory.isLim≈+₂
          (signedRootSequence y) (signedRootSequence z)
          (approximateSignedRoot y) (approximateSignedRoot z)
          (η +₊ (κ +₊ η)) η η
          (approximateSignedRoot-isLimit y)
          (approximateSignedRoot-isLimit z)
          (signedRootApproximation-pres≈ y z κ η y≈κz)
      ∣₁
    where
    gap : ℚ₊
    gap = [ ε -₊ κ ]⟨ κ<ε ⟩

    η : ℚ₊
    η = (gap /2₊) /4₊

    radius : ℚ₊
    radius = η +₊ (η +₊ (η +₊ (κ +₊ η)))

    radius<ε : radius <₊ ε
    radius<ε = begin<
      fst radius
        ≡→≤⟨ ℚ! ⟩
      fst ((η +₊ η) +₊ (η +₊ η)) + fst κ
        ≡→≤⟨ cong (_+ fst κ)
          (/4+/4+/4+/4≡id (fst (gap /2₊))) ⟩
      fst (gap /2₊) + fst κ
        <⟨ /2₊<id gap <+[ fst κ ] ⟩
      fst gap + fst κ
        ≡→≤⟨ minusPlus₊ ε κ ⟩
      fst ε ◾

signedSquareℚⁿ : NE[ ℚSignedSquarePremetricSpace , ℚPremetricSpace ]
fst signedSquareℚⁿ = signedSquareℚ
IsNonExpanding.pres≈ (snd signedSquareℚⁿ) _ _ _ = idfun _

signedSquareℚ-toCompletionⁿ :
  NE[ ℚSignedSquarePremetricSpace , OrdinaryCompletion.ℭPremetricSpace ]
signedSquareℚ-toCompletionⁿ =
  CategoryStructures._∘NE_ ιⁿ signedSquareℚⁿ

private
  module LiftSignedSquare = Liftℭ
    ℚSignedSquarePremetricSpace ℚPremetricSpace

completionSignedSquareⁿ :
  NE[ SignedCompletion.ℭPremetricSpace , OrdinaryCompletion.ℭPremetricSpace ]
completionSignedSquareⁿ = LiftSignedSquare.liftNonExpandingℭ
  signedSquareℚ-toCompletionⁿ

private
  module LiftSignedRoot = LiftCompleteCodomain
    ℚPremetricSpace SignedCompletion.ℭPremetricSpace SignedCompletion.isCompleteℭ

completionSignedRootⁿ :
  NE[ OrdinaryCompletion.ℭPremetricSpace , SignedCompletion.ℭPremetricSpace ]
completionSignedRootⁿ = LiftSignedRoot.liftNonExpanding approximateSignedRootⁿ

completionSignedSquare-ι : ∀ x →
  fst completionSignedSquareⁿ (SignedCompletion.ι x)
    ≡ OrdinaryCompletion.ι (signedSquareℚ x)
completionSignedSquare-ι x =
  funExt⁻ (LiftSignedSquare.liftⁿℭ∘ι signedSquareℚ-toCompletionⁿ) x

completionSignedRoot-ι : ∀ y →
  fst completionSignedRootⁿ (OrdinaryCompletion.ι y)
    ≡ approximateSignedRoot y
completionSignedRoot-ι y =
  funExt⁻ (LiftSignedRoot.liftⁿ∘ι approximateSignedRootⁿ) y

private
  signedRootSequence-limit-ι : ∀ x →
    SignedTheory.isLimit
      (signedRootSequence (signedSquareℚ x)) (SignedCompletion.ι x)
  signedRootSequence-limit-ι x ε θ =
    SignedCompletion.ι-ι _ x (ε +₊ θ) $ ℚ.recompute< $ begin<
      abs (signedSquareℚ (signedRootApproximation (signedSquareℚ x) ε)
        - signedSquareℚ x)
        <⟨ signedRootApproximation-close (signedSquareℚ x) ε ⟩
      fst ε
        <⟨ <₊SumLeft ε θ ⟩
      fst (ε +₊ θ) ◾

approximateSignedRoot-signedSquareℚ : ∀ x →
  approximateSignedRoot (signedSquareℚ x) ≡ SignedCompletion.ι x
approximateSignedRoot-signedSquareℚ x = cong fst $
  SignedTheory.isPropLimit (signedRootSequence (signedSquareℚ x))
    (approximateSignedRoot (signedSquareℚ x)
      , approximateSignedRoot-isLimit (signedSquareℚ x))
    (SignedCompletion.ι x , signedRootSequence-limit-ι x)

private
  completionSignedSquare-root-isLimit : ∀ y →
    OrdinaryTheory.isLimit
      (fst completionSignedSquareⁿ ∘ signedRootSequence y)
      (OrdinaryCompletion.ι y)
  completionSignedSquare-root-isLimit y ε θ =
    OrdinaryCompletion.ι-ι
      (signedSquareℚ (signedRootApproximation y ε)) y (ε +₊ θ) $
      ℚ.recompute< $ begin<
        abs (signedSquareℚ (signedRootApproximation y ε) - y)
          <⟨ signedRootApproximation-close y ε ⟩
        fst ε
          <⟨ <₊SumLeft ε θ ⟩
        fst (ε +₊ θ) ◾

completionSignedSquare-approximateSignedRoot : ∀ y →
  fst completionSignedSquareⁿ (approximateSignedRoot y) ≡ OrdinaryCompletion.ι y
completionSignedSquare-approximateSignedRoot y = cong fst $
  OrdinaryTheory.isPropLimit
    (fst completionSignedSquareⁿ ∘ signedRootSequence y)
    (fst completionSignedSquareⁿ (approximateSignedRoot y)
      , NE→presLim completionSignedSquareⁿ
          (signedRootSequence y) (approximateSignedRoot y)
          (approximateSignedRoot-isLimit y))
    (OrdinaryCompletion.ι y , completionSignedSquare-root-isLimit y)

completionSignedSquare∘completionSignedRoot :
  CategoryStructures._∘NE_ completionSignedSquareⁿ completionSignedRootⁿ
    ≡ CategoryStructures.idⁿ
completionSignedSquare∘completionSignedRoot =
  nonExpanding≡ ℚPremetricSpace OrdinaryCompletion.ℭPremetricSpace _ _ $
    funExt λ y →
      cong (fst completionSignedSquareⁿ) (completionSignedRoot-ι y)
      ∙ completionSignedSquare-approximateSignedRoot y

completionSignedRoot∘completionSignedSquare :
  CategoryStructures._∘NE_ completionSignedRootⁿ completionSignedSquareⁿ
    ≡ CategoryStructures.idⁿ
completionSignedRoot∘completionSignedSquare =
  nonExpanding≡ ℚSignedSquarePremetricSpace SignedCompletion.ℭPremetricSpace _ _ $
    funExt λ x →
      cong (fst completionSignedRootⁿ) (completionSignedSquare-ι x)
      ∙ completionSignedRoot-ι (signedSquareℚ x)
      ∙ approximateSignedRoot-signedSquareℚ x

signedSquareCompletionCatIso :
  CatIso (CategoryStructures.PremetricSpaceCategoryⁿ ℓ-zero ℓ-zero)
    SignedCompletion.ℭPremetricSpace OrdinaryCompletion.ℭPremetricSpace
fst signedSquareCompletionCatIso = completionSignedSquareⁿ
isIso.inv (snd signedSquareCompletionCatIso) = completionSignedRootⁿ
isIso.sec (snd signedSquareCompletionCatIso) =
  completionSignedSquare∘completionSignedRoot
isIso.ret (snd signedSquareCompletionCatIso) =
  completionSignedRoot∘completionSignedSquare

signedSquareCompletionPremetricSpaceEquiv :
  PremetricSpaceEquiv
    SignedCompletion.ℭPremetricSpace OrdinaryCompletion.ℭPremetricSpace
signedSquareCompletionPremetricSpaceEquiv =
  CatIso→PremetricSpaceEquiv
    SignedCompletion.ℭPremetricSpace OrdinaryCompletion.ℭPremetricSpace
    signedSquareCompletionCatIso

signedSquareCompletionEquiv : SignedCompletion.ℭ ≃ OrdinaryCompletion.ℭ
signedSquareCompletionEquiv = fst signedSquareCompletionPremetricSpaceEquiv
