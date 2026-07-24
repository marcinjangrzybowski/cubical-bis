module Cubical.HITs.CauchyReals.Complex.Examples where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Int.Fast as ℤ using (pos)
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Domain
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Within
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative.Algebra
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series
open import Cubical.HITs.CauchyReals.Complex.Transcendental.RootsOfUnity

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


gaussianProduct :
  (1ℂ +ℂ iℂ) ·ℂ (1ℂ -ℂ iℂ) ≡ fromℝ 2
gaussianProduct = ℂ≡ ℝ! ℝ!


squareDerivativeAtI :
  HasComplexDerivativeAt squareℂ (iℂ +ℂ iℂ) iℂ
squareDerivativeAtI = squareHasDerivative iℂ


squarePlusIdentityHolomorphicOnBall :
  ∀ center ε →
  HolomorphicOn (ComplexOpenBall center ε)
    (addComplexFunctions squareℂ (λ z → z))
squarePlusIdentityHolomorphicOnBall center ε =
  holomorphicOn-add
    {P = ComplexOpenBall center ε}
    {f = squareℂ} {g = λ z → z}
    (squareHolomorphicOn (ComplexOpenBall center ε))
    (identityHolomorphicOn (ComplexOpenBall center ε))


principalCubeRoot : RootOfUnity 3
principalCubeRoot = principalRootOfUnity 3


finiteGeometricIdentity : ∀ z n →
  (1ℂ -ℂ z) ·ℂ partialSumℂ (geometricTerms z) n ≡
  1ℂ -ℂ (z ^ℂ n)
finiteGeometricIdentity = geometricPartialSum


geometricHalfℚ : ℚ
geometricHalfℚ = [ pos 1 / 2 ]


geometricThreeQuarters₊ : ℚ₊
geometricThreeQuarters₊ =
  [ pos 3 / 4 ] , <≤ℚ!


geometricHalfℝ : ℝ
geometricHalfℝ = rat geometricHalfℚ


opaque
  geometricHalfℂ : ℂ
  geometricHalfℂ = fromℝ geometricHalfℝ


  geometricHalfℂ-path :
    geometricHalfℂ ≡ fromℝ geometricHalfℝ
  geometricHalfℂ-path = refl


private
  geometricHalfℝ-path :
    geometricHalfℝ ≡ rat geometricHalfℚ
  geometricHalfℝ-path = refl


  geometricHalfℝ-positive :
    0 <ᵣ geometricHalfℝ
  geometricHalfℝ-positive =
    subst (0 <ᵣ_)
      (sym geometricHalfℝ-path)
      (<ℚ→<ᵣ 0 geometricHalfℚ <≤ℚ!)


  geometricHalfModulus :
    modulus geometricHalfℂ ≡ geometricHalfℝ
  geometricHalfModulus =
    cong modulus geometricHalfℂ-path
    ∙ modulus-fromℝ geometricHalfℝ
    ∙ absᵣPos geometricHalfℝ
        geometricHalfℝ-positive


  geometricHalfℝ<ThreeQuarters :
    geometricHalfℝ <ᵣ
    rat (fst geometricThreeQuarters₊)
  geometricHalfℝ<ThreeQuarters =
    subst (_<ᵣ rat (fst geometricThreeQuarters₊))
      (sym geometricHalfℝ-path)
      (<ℚ→<ᵣ
        geometricHalfℚ
        (fst geometricThreeQuarters₊)
        <≤ℚ!)


opaque
  halfGeometricBound :
    RationalContractionBound geometricHalfℂ
  halfGeometricBound =
    geometricThreeQuarters₊ ,
    ( isTrans≡<ᵣ _ _ _
        geometricHalfModulus
        geometricHalfℝ<ThreeQuarters
    , <≤ℚ!
    )
