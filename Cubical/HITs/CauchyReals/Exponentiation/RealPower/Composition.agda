module Cubical.HITs.CauchyReals.Exponentiation.RealPower.Composition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Structure

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Relation.Nullary

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Nat as ℕ hiding (_·_;_+_)
import Cubical.Data.Nat.Mod as ℕ
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Int.Fast as ℤ using (pos; ℤ)
import Cubical.Data.Int.Fast.Order as ℤ
import Cubical.Data.Int.Fast.Properties as ℤP
import Cubical.Data.Int.Base as ℤStd
import Cubical.Data.Int.Properties as ℤStdP
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.SetQuotients as SQ hiding (_/_)

open import Cubical.Data.NatPlusOne

open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using (0<_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Floor as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Rationals.Inverse as ℚ using (invℚ)

import Cubical.Algebra.OrderedCommRing.Properties as OCRP
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals using (ℚOrderedCommRing)

module ℚO = OCRP.OrderedCommRingTheory ℚOrderedCommRing


open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Inverse.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Approximation.Bisection
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)
open import Cubical.Tactics.CauchyReals.ExpressionLifting

open import Cubical.HITs.CauchyReals.Exponentiation.Base
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Elementary using
  (seqΔ-δ; lnSeq; lnSeq'; lnSeqCont; fromSucℚ₊)
open import Cubical.HITs.CauchyReals.Exponentiation.Logarithm.Sequence.Limit

open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

import Cubical.Algebra.CommRing.Instances.Int.Fast as ℤCRing
open import Cubical.Algebra.Group.Instances.Bool
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Ring.Properties
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
import Cubical.Algebra.CommRing as CR

open import Cubical.Algebra.Group.DirProd
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Construction

open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition

private
 opaque
  rationalPower-after-realPower-cont : ∀ x q →
    IsContinuous (λ v → fst ((x ^ᵣ v) ^ℚ q))
  rationalPower-after-realPower-cont x q =
    let reconstructed : ℝ → ℝ
        reconstructed v =
          fst (((fst (x ^ᵣ v) , snd (x ^ᵣ v)) ^ℚ q))
        reconstructed-cont : IsContinuous reconstructed
        reconstructed-cont = IsContinuousWithPred∘IsContinuous
          pred0< (curry (fst ∘ (_^ℚ q))) (fst ∘ (x ^ᵣ_))
          (λ v → snd (x ^ᵣ v)) (IsContinuous^ℚ q) (cont-^ x)
        function-path : reconstructed ≡
          (λ v → fst ((x ^ᵣ v) ^ℚ q))
        function-path = funExt λ v → cong (λ z → fst (z ^ℚ q))
          (ℝ₊≡
            {x = (fst (x ^ᵣ v) , snd (x ^ᵣ v))}
            {y = x ^ᵣ v} refl)
    in subst IsContinuous function-path reconstructed-cont

realPowerMulExponent : (x : ℝ₊) (a b : ℝ) →
  fst ((x ^ᵣ a) ^ᵣ b) ≡ fst (x ^ᵣ (a ·ᵣ b))
realPowerMulExponent x a =
  ≡Continuous
    (fst ∘ ((x ^ᵣ a) ^ᵣ_))
    ((fst ∘ (x ^ᵣ_)) ∘ (a ·ᵣ_))
    (cont-^ (x ^ᵣ a))
    (IsContinuous∘ (fst ∘ (x ^ᵣ_)) (a ·ᵣ_)
      (cont-^ x) (IsContinuous·ᵣL a))
    λ b' →
      ^-rat (x ^ᵣ a) b'
      ∙ ≡Continuous
          (λ v → fst ((x ^ᵣ v) ^ℚ b'))
          ((fst ∘ (x ^ᵣ_)) ∘ (_·ᵣ rat b'))
          (rationalPower-after-realPower-cont x b')
          (IsContinuous∘ (fst ∘ (x ^ᵣ_)) (_·ᵣ rat b')
            (cont-^ x) (IsContinuous·ᵣR (rat b')))
          (λ a' →
            cong (λ z → fst (z ^ℚ b'))
              (ℝ₊≡ {x = x ^ᵣ rat a'} {y = x ^ℚ a'} (^-rat x a'))
            ∙ cong fst (^ℚ-· x a' b')
            ∙ sym (^-rat x (a' ℚ.· b'))
            ∙ cong (fst ∘ (x ^ᵣ_)) (rat·ᵣrat a' b'))
          a
