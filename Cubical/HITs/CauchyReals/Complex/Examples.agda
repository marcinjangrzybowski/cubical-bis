module Cubical.HITs.CauchyReals.Complex.Examples where

open import Cubical.Foundations.Prelude

open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Calculus.Derivative
open import Cubical.HITs.CauchyReals.Complex.Analysis.Series
open import Cubical.HITs.CauchyReals.Complex.Transcendental.RootsOfUnity

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


gaussianProduct :
  (1ℂ +ℂ iℂ) ·ℂ (1ℂ -ℂ iℂ) ≡ fromℝ 2
gaussianProduct = ℂ≡ ℝ! ℝ!


squareDerivativeAtI :
  HasComplexDerivativeAt squareℂ (iℂ +ℂ iℂ) iℂ
squareDerivativeAtI = squareHasDerivative iℂ


principalCubeRoot : RootOfUnity 3
principalCubeRoot = principalRootOfUnity 3


finiteGeometricIdentity : ∀ z n →
  (1ℂ -ℂ z) ·ℂ partialSumℂ (geometricTerms z) n ≡
  1ℂ -ℂ (z ^ℂ n)
finiteGeometricIdentity = geometricPartialSum
