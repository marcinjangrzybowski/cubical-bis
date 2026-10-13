module Cubical.Analysis.Complex.Polynomial.Newton where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing using (ℝCommRing)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (0≤→isNonnegative)
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Contraction
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Differential.Monic
open import Cubical.Analysis.Complex.Polynomial.Newton.Bounds
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.LocalRoots
  using (NewtonErrorBound; LocalNewtonRootTheorem)
import Cubical.Analysis.Complex.Polynomial.Newton.Algebra as NewtonDefinition

private
  module C = NewtonDefinition.NewtonIdentities ℂCommRing
  module R = NewtonDefinition.NewtonIdentities ℝCommRing

-- A fixed derivative is inverted once. The existing contraction theorem
-- constructs the entire iteration and its native Cauchy witness.
module NewtonConstruction (n : ℕ) (p : MonicPolynomial n) (center inverse : ℂ)
  (radius error q : ℝ)
  (inverseLaw : inverse ·ℂ derivativeMonic p center ≡ 1ℂ)
  (radius-positive : 0ℝ <ℝ radius)
  (error-nonnegative : 0ℝ ≤ℝ error)
  (q-nonnegative : 0ℝ ≤ℝ q) (q<one : q <ℝ 1ℝ)
  (inverseBound : normℂ inverse · error ≤ℝ q)
  (correctionBound : normℂ (inverse ·ℂ evaluateMonic p center) ≤ℝ (1ℝ - q) · radius)
  (remainderBound : NewtonErrorBound p center radius error) where

  private
    f : ℂ → ℂ
    f z = z -ℂ inverse ·ℂ evaluateMonic p z

    radius-nonnegative : 0ℝ ≤ℝ radius
    radius-nonnegative = <ℝ-weaken 0ℝ radius radius-positive

    center-inBall : ComplexBall center radius center
    center-inBall = subst (_≤ℝ radius)
      (sym (cong normℂ (+ℂInvR center) ∙ normℂ-zero)) radius-nonnegative

    opaque
      contracts : ∀ z w → ComplexBall center radius z → ComplexBall center radius w →
        normℂ (f z -ℂ f w) ≤ℝ q · normℂ (z -ℂ w)
      contracts z w zb wb = newtonDifferenceBound inverse (derivativeMonic p center) inverseLaw
        z w (evaluateMonic p z) (evaluateMonic p w) error q inverseBound (remainderBound z w zb wb)

      contractsToCenter : ∀ z → ComplexBall center radius z →
        normℂ (f z -ℂ f center) ≤ℝ q · radius
      contractsToCenter z zb =
        ≤ℝ-trans (normℂ (f z -ℂ f center)) (q · normℂ (z -ℂ center)) (q · radius)
          (contracts z center zb center-inBall)
          (mulPres≤L (normℂ (z -ℂ center)) radius q (0≤→isNonnegative q q-nonnegative) zb)

      correctionAtCenter : normℂ (f center -ℂ center) ≤ℝ (1ℝ - q) · radius
      correctionAtCenter = subst (_≤ℝ (1ℝ - q) · radius)
        (sym (newtonCorrectionNorm inverse center (evaluateMonic p center))) correctionBound

      preserves : ∀ z → ComplexBall center radius z → ComplexBall center radius (f z)
      preserves z zb = subst (_≤ℝ radius)
        (sym (cong normℂ (C.aroundCenter (f z) (f center) center)))
        (subst (normℂ ((f z -ℂ f center) +ℂ (f center -ℂ center)) ≤ℝ_)
          (R.preserveRadius q radius)
          (normℂ-addBound (f z -ℂ f center) (f center -ℂ center)
            (q · radius) ((1ℝ - q) · radius) (contractsToCenter z zb) correctionAtCenter))

    module I = Iteration f center radius q radius-nonnegative q-nonnegative q<one preserves contracts

  opaque
    root : ℂ
    root = I.value

    root-inBall : ComplexBall center radius root
    root-inBall = I.value-inBall

    root-equation : evaluateMonic p root ≡ 0ℂ
    root-equation = C.fixedToRoot inverse (derivativeMonic p center) inverseLaw
      root (evaluateMonic p root) I.value-fixed

    root-unique : ∀ z → ComplexBall center radius z → evaluateMonic p z ≡ 0ℂ → z ≡ root
    root-unique z zb equation = I.value-unique z zb
      (C.rootToFixed inverse z (evaluateMonic p z) equation)

-- An inhabitant of the previously checked statement, including an actual
-- root and uniqueness in the ball. The quantitative premises remain explicit;
-- deriving them from separability and approximate FTA is subsequent work.
localNewtonRoot : LocalNewtonRootTheorem
localNewtonRoot n p center inverse radius error q inverseLaw rp en qn q<1 inverseBound correctionBound remainderBound =
  N.root , N.root-inBall , N.root-equation , N.root-unique
  where
  module N = NewtonConstruction n p center inverse radius error q inverseLaw
    rp en qn q<1 inverseBound correctionBound remainderBound
