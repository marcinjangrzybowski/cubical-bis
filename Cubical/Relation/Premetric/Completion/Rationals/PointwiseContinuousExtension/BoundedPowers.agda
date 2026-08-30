module Cubical.Relation.Premetric.Completion.Rationals.PointwiseContinuousExtension.BoundedPowers where

-- This experiment constructs powers on the native rational completion from
-- bounded Lipschitz multiplication.  In particular, it does not import the
-- (unbounded) multiplication or power operations on Cauchy reals.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ hiding (isProp∼)
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Bounded

import Cubical.Relation.Premetric.Completion.Lift.PointwiseContinuousExtension
  as PointwiseExtensionDefinition
import Cubical.Relation.Premetric.Completion.Rationals.PointwiseContinuousExtension.LocalRepresentatives
  as LocalRepresentatives
import Cubical.Relation.Premetric.Completion.Rationals.PointwiseContinuousExtension.LocallyUniformRepresentatives
  as LocallyUniformRepresentatives

module E = PointwiseExtensionDefinition ℚPremetricSpace ℚPremetricSpace
module LR = LocalRepresentatives
module LUR = LocallyUniformRepresentatives

open PositiveRationals
open PositiveHalvesℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing

private
  module Pℚ = PremetricStr (ℚPremetricSpace .snd)
  module Pℝ = PremetricStr (ℝPremetricSpace .snd)
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


-- A rational anchor close to x gives a ball containing every sufficiently
-- close rational approximation of x.  The anchor itself remains truncated.

anchorBound : ℚ → ℚ₊
anchorBound a = (1 +₊ 1) +₊ ℚ.maxWithPos 1 (abs a)


closeToAnchor-bounded : ∀ a q →
  q Pℚ.≈[ 1 +₊ 1 ] a → abs q ≤ℚ fst (anchorBound a)
closeToAnchor-bounded a q q≈a = begin≤
  abs q
    ≡→≤⟨ sym (cong abs
      (cong (q ℚ.+_) ℚRing.0Selfinverse ∙ ℚ.+IdR q)) ⟩
  abs (q ℚ.- 0)
    ≤⟨ triangularInequality- q 0 a ⟩
  abs (q ℚ.- a) ℚ.+ abs (a ℚ.- 0)
    ≡→≤⟨ cong (abs (q ℚ.- a) ℚ.+_)
      (cong abs
        (cong (a ℚ.+_) ℚRing.0Selfinverse ∙ ℚ.+IdR a)) ⟩
  abs (q ℚ.- a) ℚ.+ abs a
    <⟨ +MonoR< _ _ (abs a) q≈a ⟩
  fst (1 +₊ 1) ℚ.+ abs a
    ≤⟨ +MonoL≤ (abs a) (fst (ℚ.maxWithPos 1 (abs a)))
      (fst (1 +₊ 1)) (ℚ.≤max' 1 (abs a)) ⟩
  fst (anchorBound a) ◾


approximation-bounded : ∀ a x q δ →
  rat a Pℝ.≈[ 1 ] x →
  δ <₊ 1 →
  rat q Pℝ.≈[ δ ] x →
  abs q ≤ℚ fst (anchorBound a)
approximation-bounded a x q δ rata∼x δ<1 ratq∼x =
  closeToAnchor-bounded a q
    (rat-rat-toAbs q a (1 +₊ 1)
      (Pℝ.isMonotone≈< (rat q) (rat a) (δ +₊ 1) (1 +₊ 1)
        (+MonoR< (fst δ) 1 1 δ<1)
        (Pℝ.isTriangular≈ (rat q) x (rat a) δ 1
          ratq∼x (Pℝ.isSym≈ (rat a) x 1 rata∼x))))


squareℚ : ℚ → ℚ
squareℚ q = q ℚ.· q


boundedSquare : ℚ₊ → ℝ → ℝ
boundedSquare B x = boundedMulℝ B x x


boundedSquareIsLipschitz : ∀ B →
  IsLipschitzWith
    (ℝPremetricSpace .snd) (boundedSquare B)
    (ℝPremetricSpace .snd) (B +₊ B)
boundedSquareIsLipschitz B
  .IsLipschitzWith.pres≈ x y ε x∼y =
  Pℝ.subst≈ (boundedSquare B x) (boundedSquare B y)
    (sym (ℚ.·DistR+ (fst B) (fst B) (fst ε)))
    (Pℝ.isTriangular≈
      (boundedMulℝ B x x) (boundedMulℝ B y x)
      (boundedMulℝ B y y) (B ·₊ ε) (B ·₊ ε)
      (boundedMulIsLipschitz₁At B x
        .IsLipschitzWith.pres≈ x y ε x∼y)
      (boundedMulIsLipschitz₂ B y
        .IsLipschitzWith.pres≈ x y ε x∼y))


boundedSquare-isContinuous : ∀ B →
  isContinuous
    (ℝPremetricSpace .snd) (boundedSquare B)
    (ℝPremetricSpace .snd)
boundedSquare-isContinuous B =
  isLipschitz→isContinuous
    (ℝPremetricSpace .snd) (boundedSquare B) (ℝPremetricSpace .snd)
    ∣ (B +₊ B) , boundedSquareIsLipschitz B ∣₁


private
  absToBounds : ∀ (B : ℚ₊) (q : ℚ) → abs q ≤ℚ fst B →
    (ℚ.- fst B ≤ℚ q) × (q ≤ℚ fst B)
  absToBounds B q absq≤B .fst =
    subst (ℚ.- fst B ≤ℚ_) (ℚ.-Invol q)
      (ℚ.minus-≤ (ℚ.- q) (fst B)
        (isTrans≤ (ℚ.- q) (abs q) (fst B)
          (-≤abs q) absq≤B))
  absToBounds B q absq≤B .snd =
    isTrans≤ q (abs q) (fst B) (≤abs q) absq≤B


boundedSquare-rat-within : ∀ B q →
  abs q ≤ℚ fst B →
  boundedSquare B (rat q) ≡ rat (squareℚ q)
boundedSquare-rat-within B q absq≤B =
  boundedMul-rat-within B q q
    (absToBounds B q absq≤B .fst)
    (absToBounds B q absq≤B .snd)
    (absToBounds B q absq≤B .fst)
    (absToBounds B q absq≤B .snd)


squareRepresentativeFromAnchor : ∀ a x →
  rat a Pℝ.≈[ 1 ] x →
  LR.LocalContinuousRepresentativeAt (rat ∘ squareℚ) x
squareRepresentativeFromAnchor a x anchor =
  boundedSquare B ,
  boundedSquare-isContinuous B ,
  (1 /2₊) ,
  λ q ratq∼x →
    boundedSquare-rat-within B q
      (approximation-bounded a x q (1 /2₊) anchor
        (/2₊<id 1) ratq∼x)
  where
  B = anchorBound a


square-tends-from-anchor : ∀ a x →
  rat a Pℝ.≈[ 1 ] x →
  E.TendsToAt (rat ∘ squareℚ) x
    (boundedSquare (anchorBound a) x)
square-tends-from-anchor a x anchor =
  LR.localContinuousRepresentative-tends
    (rat ∘ squareℚ) x
    (squareRepresentativeFromAnchor a x anchor)


squareRestriction-merelyLocallyRepresentable :
  LR.IsMerelyLocallyContinuouslyRepresentable (rat ∘ squareℚ)
squareRestriction-merelyLocallyRepresentable x =
  PT.map
    (λ (a , anchor) → squareRepresentativeFromAnchor a x anchor)
    (∃ratApprox x 1)


squareUniformRepresentativeFromAnchor : ∀ a x →
  rat a Pℝ.≈[ 1 ] x →
  LUR.LocalUniformRepresentativeAt (rat ∘ squareℚ) x
squareUniformRepresentativeFromAnchor a x anchor =
  boundedSquare B ,
  (1 /2₊) ,
  LUR.lipschitz→uniformlyContinuousOnNeighborhood
    (boundedSquare B) x (1 /2₊)
    ∣ (B +₊ B) , boundedSquareIsLipschitz B ∣₁ ,
  λ q ratq∼x →
    boundedSquare-rat-within B q
      (approximation-bounded a x q (1 /2₊) anchor
        (/2₊<id 1) ratq∼x)
  where
  B = anchorBound a


squareRestriction-merelyLocallyUniformlyRepresentable :
  LUR.IsMerelyLocallyUniformlyRepresentable (rat ∘ squareℚ)
squareRestriction-merelyLocallyUniformlyRepresentable x =
  PT.map
    (λ (a , anchor) →
      squareUniformRepresentativeFromAnchor a x anchor)
    (∃ratApprox x 1)


squareRestriction-everywhereConvergent :
  E.IsEverywhereConvergent (rat ∘ squareℚ)
squareRestriction-everywhereConvergent =
  LUR.merelyLocallyUniformlyRepresentable→everywhereConvergent
    (rat ∘ squareℚ)
    squareRestriction-merelyLocallyUniformlyRepresentable


squareℝ-fromBoundedLifts : ℝ → ℝ
squareℝ-fromBoundedLifts =
  E.liftEverywhereConvergent
    (rat ∘ squareℚ) squareRestriction-everywhereConvergent


squareℝ-fromBoundedLifts-rat : ∀ q →
  squareℝ-fromBoundedLifts (rat q) ≡ rat (squareℚ q)
squareℝ-fromBoundedLifts-rat =
  E.liftEverywhereConvergent-ι
    (rat ∘ squareℚ) squareRestriction-everywhereConvergent


squareℝ-fromBoundedLifts-isContinuous :
  isContinuous
    (ℝPremetricSpace .snd) squareℝ-fromBoundedLifts
    (ℝPremetricSpace .snd)
squareℝ-fromBoundedLifts-isContinuous =
  E.liftEverywhereConvergent-isContinuous
    (rat ∘ squareℚ) squareRestriction-everywhereConvergent


squareℝ-fromBoundedLifts-isLocallyUniformlyContinuous :
  LUR.IsLocallyUniformlyContinuous squareℝ-fromBoundedLifts
squareℝ-fromBoundedLifts-isLocallyUniformlyContinuous =
  LUR.localUniformRepresentatives→extensionLocallyUniformlyContinuous
    (rat ∘ squareℚ)
    squareRestriction-merelyLocallyUniformlyRepresentable
    squareℝ-fromBoundedLifts
    (E.liftEverywhereConvergent-tends
      (rat ∘ squareℚ) squareRestriction-everywhereConvergent)


-- Any concrete anchor computes the same value.  Thus truncation hides only
-- the localization choice; it does not hide an arbitrary output value.

squareℝ-at-anchor : ∀ a x →
  rat a Pℝ.≈[ 1 ] x →
  squareℝ-fromBoundedLifts x ≡ boundedSquare (anchorBound a) x
squareℝ-at-anchor a x anchor =
  E.tendsToAt-unique x
    (squareℝ-fromBoundedLifts x)
    (boundedSquare (anchorBound a) x)
    (E.liftEverywhereConvergent-tends
      (rat ∘ squareℚ) squareRestriction-everywhereConvergent x)
    (square-tends-from-anchor a x anchor)


-- Natural powers
-- --------------
--
-- The same idea iterates.  At stage k+1 the bounded multiplier must contain
-- both q and q^k.  The sum B + B^k is a deliberately generous positive
-- bound, and avoids any case split involving whether B is below or above 1.

powℚ : ℕ → ℚ → ℚ
powℚ n q = q ℚ.^ⁿ n


private
  powAbs : ∀ q n → abs (powℚ n q) ≡ (abs q) ℚ.^ⁿ n
  powAbs q zero = 0<→abs≡id 1 0<1
  powAbs q (suc n) =
    sym (abs·abs q (powℚ n q))
    ∙ cong (abs q ·_) (powAbs q n)

  powBounded : ∀ B q n →
    abs q ≤ℚ fst B →
    abs (powℚ n q) ≤ℚ fst (B ℚ₊^ⁿ n)
  powBounded B q n absq≤B =
    subst (_≤ℚ fst (B ℚ₊^ⁿ n))
      (sym (powAbs q n))
      (powMono n (0≤abs q) absq≤B)


powerStageBound : ℚ₊ → ℕ → ℚ₊
powerStageBound B n = B +₊ (B ℚ₊^ⁿ n)


private
  input≤powerStageBound : ∀ B n →
    fst B ≤ℚ fst (powerStageBound B n)
  input≤powerStageBound B n =
    ≤SumLeftNonNeg (fst B) (fst (B ℚ₊^ⁿ n))
      (ℚ.0≤ℚ₊ (B ℚ₊^ⁿ n))

  output≤powerStageBound : ∀ B n →
    fst (B ℚ₊^ⁿ n) ≤ℚ fst (powerStageBound B n)
  output≤powerStageBound B n =
    ≤SumRightNonNeg (fst (B ℚ₊^ⁿ n)) (fst B)
      (ℚ.0≤ℚ₊ B)


-- Every multiplication used here is one of the already available bounded
-- Lipschitz lifts.  There is no recursive call to unbounded real
-- multiplication.

boundedPower : ℚ₊ → ℕ → ℝ → ℝ
boundedPower B zero x = rat 1
boundedPower B (suc n) x =
  boundedMulℝ (powerStageBound B n) x (boundedPower B n x)


boundedPower-rat-within : ∀ B n q →
  abs q ≤ℚ fst B →
  boundedPower B n (rat q) ≡ rat (powℚ n q)
boundedPower-rat-within B zero q absq≤B = refl
boundedPower-rat-within B (suc n) q absq≤B =
  cong (boundedMulℝ D (rat q))
    (boundedPower-rat-within B n q absq≤B)
  ∙ boundedMul-rat-within D q (powℚ n q)
      (absToBounds D q q-bounded .fst)
      (absToBounds D q q-bounded .snd)
      (absToBounds D (powℚ n q) qⁿ-bounded .fst)
      (absToBounds D (powℚ n q) qⁿ-bounded .snd)
  where
  D = powerStageBound B n

  q-bounded : abs q ≤ℚ fst D
  q-bounded = isTrans≤ (abs q) (fst B) (fst D)
    absq≤B (input≤powerStageBound B n)

  qⁿ-bounded : abs (powℚ n q) ≤ℚ fst D
  qⁿ-bounded = isTrans≤
    (abs (powℚ n q)) (fst (B ℚ₊^ⁿ n)) (fst D)
    (powBounded B q n absq≤B)
    (output≤powerStageBound B n)


powerLipschitzConstant : ℚ₊ → ℕ → ℚ₊
powerLipschitzConstant B zero = 1
powerLipschitzConstant B (suc n) =
  powerStageBound B n +₊
    (powerStageBound B n ·₊ powerLipschitzConstant B n)


boundedPowerIsLipschitz : ∀ B n →
  IsLipschitzWith
    (ℝPremetricSpace .snd) (boundedPower B n)
    (ℝPremetricSpace .snd) (powerLipschitzConstant B n)
boundedPowerIsLipschitz B zero
  .IsLipschitzWith.pres≈ x y ε x∼y =
  Pℝ.isRefl≈ (rat 1) (powerLipschitzConstant B zero ·₊ ε)
boundedPowerIsLipschitz B (suc n)
  .IsLipschitzWith.pres≈ x y ε x∼y =
  Pℝ.subst≈
    (boundedPower B (suc n) x)
    (boundedPower B (suc n) y)
    factor
    (Pℝ.isTriangular≈
      (boundedMulℝ D x (boundedPower B n x))
      (boundedMulℝ D y (boundedPower B n x))
      (boundedMulℝ D y (boundedPower B n y))
      (D ·₊ ε) (D ·₊ (L ·₊ ε))
      (boundedMulIsLipschitz₁At D (boundedPower B n x)
        .IsLipschitzWith.pres≈ x y ε x∼y)
      (boundedMulIsLipschitz₂ D y
        .IsLipschitzWith.pres≈
          (boundedPower B n x) (boundedPower B n y) (L ·₊ ε)
          (boundedPowerIsLipschitz B n
            .IsLipschitzWith.pres≈ x y ε x∼y)))
  where
  D = powerStageBound B n
  L = powerLipschitzConstant B n

  factor :
    fst (D ·₊ ε +₊ D ·₊ (L ·₊ ε)) ≡
    fst (powerLipschitzConstant B (suc n) ·₊ ε)
  factor =
    cong (fst (D ·₊ ε) ℚ.+_)
      (ℚ.·Assoc (fst D) (fst L) (fst ε))
    ∙ sym (ℚ.·DistR+
      (fst D) (fst D ℚ.· fst L) (fst ε))


boundedPower-isContinuous : ∀ B n →
  isContinuous
    (ℝPremetricSpace .snd) (boundedPower B n)
    (ℝPremetricSpace .snd)
boundedPower-isContinuous B n =
  isLipschitz→isContinuous
    (ℝPremetricSpace .snd) (boundedPower B n)
    (ℝPremetricSpace .snd)
    ∣ powerLipschitzConstant B n , boundedPowerIsLipschitz B n ∣₁


powerRepresentativeFromAnchor : ∀ n a x →
  rat a Pℝ.≈[ 1 ] x →
  LR.LocalContinuousRepresentativeAt (rat ∘ powℚ n) x
powerRepresentativeFromAnchor n a x anchor =
  boundedPower B n ,
  boundedPower-isContinuous B n ,
  (1 /2₊) ,
  λ q ratq∼x →
    boundedPower-rat-within B n q
      (approximation-bounded a x q (1 /2₊) anchor
        (/2₊<id 1) ratq∼x)
  where
  B = anchorBound a


power-tends-from-anchor : ∀ n a x →
  rat a Pℝ.≈[ 1 ] x →
  E.TendsToAt (rat ∘ powℚ n) x
    (boundedPower (anchorBound a) n x)
power-tends-from-anchor n a x anchor =
  LR.localContinuousRepresentative-tends
    (rat ∘ powℚ n) x
    (powerRepresentativeFromAnchor n a x anchor)


powerRestriction-merelyLocallyRepresentable : ∀ n →
  LR.IsMerelyLocallyContinuouslyRepresentable (rat ∘ powℚ n)
powerRestriction-merelyLocallyRepresentable n x =
  PT.map
    (λ (a , anchor) → powerRepresentativeFromAnchor n a x anchor)
    (∃ratApprox x 1)


powerUniformRepresentativeFromAnchor : ∀ n a x →
  rat a Pℝ.≈[ 1 ] x →
  LUR.LocalUniformRepresentativeAt (rat ∘ powℚ n) x
powerUniformRepresentativeFromAnchor n a x anchor =
  boundedPower B n ,
  (1 /2₊) ,
  LUR.lipschitz→uniformlyContinuousOnNeighborhood
    (boundedPower B n) x (1 /2₊)
    ∣ powerLipschitzConstant B n , boundedPowerIsLipschitz B n ∣₁ ,
  λ q ratq∼x →
    boundedPower-rat-within B n q
      (approximation-bounded a x q (1 /2₊) anchor
        (/2₊<id 1) ratq∼x)
  where
  B = anchorBound a


powerRestriction-merelyLocallyUniformlyRepresentable : ∀ n →
  LUR.IsMerelyLocallyUniformlyRepresentable (rat ∘ powℚ n)
powerRestriction-merelyLocallyUniformlyRepresentable n x =
  PT.map
    (λ (a , anchor) →
      powerUniformRepresentativeFromAnchor n a x anchor)
    (∃ratApprox x 1)


powerRestriction-everywhereConvergent : ∀ n →
  E.IsEverywhereConvergent (rat ∘ powℚ n)
powerRestriction-everywhereConvergent n =
  LUR.merelyLocallyUniformlyRepresentable→everywhereConvergent
    (rat ∘ powℚ n)
    (powerRestriction-merelyLocallyUniformlyRepresentable n)


powerℝ-fromBoundedLifts : ℕ → ℝ → ℝ
powerℝ-fromBoundedLifts n =
  E.liftEverywhereConvergent
    (rat ∘ powℚ n) (powerRestriction-everywhereConvergent n)


powerℝ-fromBoundedLifts-rat : ∀ n q →
  powerℝ-fromBoundedLifts n (rat q) ≡ rat (powℚ n q)
powerℝ-fromBoundedLifts-rat n =
  E.liftEverywhereConvergent-ι
    (rat ∘ powℚ n) (powerRestriction-everywhereConvergent n)


powerℝ-fromBoundedLifts-isContinuous : ∀ n →
  isContinuous
    (ℝPremetricSpace .snd) (powerℝ-fromBoundedLifts n)
    (ℝPremetricSpace .snd)
powerℝ-fromBoundedLifts-isContinuous n =
  E.liftEverywhereConvergent-isContinuous
    (rat ∘ powℚ n) (powerRestriction-everywhereConvergent n)


powerℝ-fromBoundedLifts-isLocallyUniformlyContinuous : ∀ n →
  LUR.IsLocallyUniformlyContinuous (powerℝ-fromBoundedLifts n)
powerℝ-fromBoundedLifts-isLocallyUniformlyContinuous n =
  LUR.localUniformRepresentatives→extensionLocallyUniformlyContinuous
    (rat ∘ powℚ n)
    (powerRestriction-merelyLocallyUniformlyRepresentable n)
    (powerℝ-fromBoundedLifts n)
    (E.liftEverywhereConvergent-tends
      (rat ∘ powℚ n) (powerRestriction-everywhereConvergent n))


powerℝ-at-anchor : ∀ n a x →
  rat a Pℝ.≈[ 1 ] x →
  powerℝ-fromBoundedLifts n x ≡
    boundedPower (anchorBound a) n x
powerℝ-at-anchor n a x anchor =
  E.tendsToAt-unique x
    (powerℝ-fromBoundedLifts n x)
    (boundedPower (anchorBound a) n x)
    (E.liftEverywhereConvergent-tends
      (rat ∘ powℚ n) (powerRestriction-everywhereConvergent n) x)
    (power-tends-from-anchor n a x anchor)
