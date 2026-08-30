module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular.Lattice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open OrderedCommRingTheory ℚOrderedCommRing

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.HITs.CauchyRealsP.Foundation.Closeness as CR
import Cubical.HITs.CauchyRealsP.Algebra.Negation as CRNeg
import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue as CRAbs
import Cubical.HITs.CauchyRealsP.Algebra.Order.Base as CROrder
import Cubical.HITs.CauchyRealsP.Algebra.Addition as CRAdd
import Cubical.HITs.CauchyRealsP.Algebra.Lattice as CRLattice
import Cubical.HITs.CauchyRealsP.Algebra.Multiplication as CRMul
import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Continuity as CRMulCont
import Cubical.HITs.CauchyRealsP.Algebra.Extensionality as CRExt

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as RealNeg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as RealAbs
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as RealAdd
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base
  as RealScalar
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
  as RealLattice
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular
  as Comparison
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular.Algebra
  as ComparisonAlgebra


private
  bodyBound : ℚ₊
  bodyBound = 1 +₊ 1

  formulaBound : ℚ₊
  formulaBound =
    RealScalar.rationalScalarBound RealLattice.rationalHalf ·₊ bodyBound

  regularMaxBody : CR.ℝ → CR.ℝ → CR.ℝ
  regularMaxBody x y =
    CRAdd._+_ (CRAdd._+_ x y)
      (CRAbs.absℝ (CRAdd._+_ x (CRNeg.- y)))

  regularFormulaMax : CR.ℝ → CR.ℝ → CR.ℝ
  regularFormulaMax x y =
    CRMul._·_ (CR.rat RealLattice.rationalHalf)
      (regularMaxBody x y)

  maxBodyIsLipschitz₁ : ∀ y →
    IsLipschitzWith (CR.ℝPremetricSpace .snd)
      (λ x → regularMaxBody x y)
      (CR.ℝPremetricSpace .snd) bodyBound
  maxBodyIsLipschitz₁ y .IsLipschitzWith.pres≈ x x' ε x∼x' =
    CR.subst∼ _ _
      {ε = ε +₊ ε} {ε' = bodyBound ·₊ ε} ℚ!
      (CRAdd.addPres∼ _ _ _ _ ε ε
        (CRAdd.addPres∼₁ x x' y ε x∼x')
        (CRAbs.absIsNonExpanding .IsNonExpanding.pres≈ _ _ ε
          (CRAdd.addPres∼₁ x x' (CRNeg.- y) ε x∼x')))

  maxBodyIsLipschitz₂ : ∀ x →
    IsLipschitzWith (CR.ℝPremetricSpace .snd)
      (regularMaxBody x)
      (CR.ℝPremetricSpace .snd) bodyBound
  maxBodyIsLipschitz₂ x .IsLipschitzWith.pres≈ y y' ε y∼y' =
    CR.subst∼ _ _
      {ε = ε +₊ ε} {ε' = bodyBound ·₊ ε} ℚ!
      (CRAdd.addPres∼ _ _ _ _ ε ε
        (CRAdd.addPres∼₂ x y y' ε y∼y')
        (CRAbs.absIsNonExpanding .IsNonExpanding.pres≈ _ _ ε
          (CRAdd.addPres∼₂ x (CRNeg.- y) (CRNeg.- y') ε
            (CRNeg.negIsNonExpanding .IsNonExpanding.pres≈
              y y' ε y∼y'))))

  rationalHalfBounded :
    CRAbs.absℝ (CR.rat RealLattice.rationalHalf) CROrder.≤ℝ
      CR.rat (fst (RealScalar.rationalScalarBound
        RealLattice.rationalHalf))
  rationalHalfBounded =
    subst
      (CROrder._≤ℝ CR.rat (fst (RealScalar.rationalScalarBound
        RealLattice.rationalHalf)))
      (sym (CRAbs.abs-rat RealLattice.rationalHalf))
      (CROrder.≤ℚ→≤ℝ (abs RealLattice.rationalHalf)
        (fst (RealScalar.rationalScalarBound RealLattice.rationalHalf))
        (ℚ.≤max' 1 (abs RealLattice.rationalHalf)))

  formulaScalarIsLipschitz :
    IsLipschitzWith (CR.ℝPremetricSpace .snd)
      (CRMul._·_ (CR.rat RealLattice.rationalHalf))
      (CR.ℝPremetricSpace .snd)
      (RealScalar.rationalScalarBound RealLattice.rationalHalf)
  formulaScalarIsLipschitz =
    CRMulCont.mulIsLipschitzLAtBound
      (RealScalar.rationalScalarBound RealLattice.rationalHalf)
      (CR.rat RealLattice.rationalHalf) rationalHalfBounded

  formulaMaxIsLipschitz₁ : ∀ y →
    IsLipschitzWith (CR.ℝPremetricSpace .snd)
      (λ x → regularFormulaMax x y)
      (CR.ℝPremetricSpace .snd) formulaBound
  formulaMaxIsLipschitz₁ y =
    CRExt.composeRealLipschitzWith
      (CRMul._·_ (CR.rat RealLattice.rationalHalf))
      (λ x → regularMaxBody x y)
      (RealScalar.rationalScalarBound RealLattice.rationalHalf)
      bodyBound formulaScalarIsLipschitz (maxBodyIsLipschitz₁ y)

  formulaMaxIsLipschitz₂ : ∀ x →
    IsLipschitzWith (CR.ℝPremetricSpace .snd)
      (regularFormulaMax x)
      (CR.ℝPremetricSpace .snd) formulaBound
  formulaMaxIsLipschitz₂ x =
    CRExt.composeRealLipschitzWith
      (CRMul._·_ (CR.rat RealLattice.rationalHalf))
      (regularMaxBody x)
      (RealScalar.rationalScalarBound RealLattice.rationalHalf)
      bodyBound formulaScalarIsLipschitz (maxBodyIsLipschitz₂ x)

  formulaMax-isLipschitz₁ : ∀ y →
    isLipschitz (CR.ℝPremetricSpace .snd)
      (λ x → regularFormulaMax x y)
      (CR.ℝPremetricSpace .snd)
  formulaMax-isLipschitz₁ y =
    ∣ formulaBound , formulaMaxIsLipschitz₁ y ∣₁

  formulaMax-isLipschitz₂ : ∀ x →
    isLipschitz (CR.ℝPremetricSpace .snd)
      (regularFormulaMax x)
      (CR.ℝPremetricSpace .snd)
  formulaMax-isLipschitz₂ x =
    ∣ formulaBound , formulaMaxIsLipschitz₂ x ∣₁

  max-isLipschitz₁ : ∀ y →
    isLipschitz (CR.ℝPremetricSpace .snd)
      (λ x → CRLattice.maxℝ x y) (CR.ℝPremetricSpace .snd)
  max-isLipschitz₁ y =
    isNonExpanding→isLipschitz
      (CR.ℝPremetricSpace .snd) _ (CR.ℝPremetricSpace .snd)
      (CRLattice.maxIsNonExpanding₁ y)

  max-isLipschitz₂ : ∀ x →
    isLipschitz (CR.ℝPremetricSpace .snd)
      (CRLattice.maxℝ x) (CR.ℝPremetricSpace .snd)
  max-isLipschitz₂ x =
    isNonExpanding→isLipschitz
      (CR.ℝPremetricSpace .snd) _ (CR.ℝPremetricSpace .snd)
      (CRLattice.maxIsNonExpanding₂ x)

  formulaMax-rat : ∀ p q →
    regularFormulaMax (CR.rat p) (CR.rat q) ≡
    CR.rat (ℚ.max p q)
  formulaMax-rat p q =
    cong (CRMul._·_ (CR.rat RealLattice.rationalHalf))
      (cong₂ CRAdd._+_
        (CRAdd.rat+rat p q)
        (cong CRAbs.absℝ
          (cong (CRAdd._+_ (CR.rat p)) (CRNeg.neg-rat q)
          ∙ CRAdd.rat+rat p (ℚR.- q))
        ∙ CRAbs.abs-rat (p ℚR.- q))
      ∙ CRAdd.rat+rat (p ℚR.+ q) (abs (p ℚR.- q)))
    ∙ CRMul.mul-rat RealLattice.rationalHalf
        ((p ℚR.+ q) ℚR.+ abs (p ℚR.- q))
    ∙ cong CR.rat (RealLattice.rationalMaxFormula p q)


regularFormulaMax≡max : ∀ x y →
  regularFormulaMax x y ≡ CRLattice.maxℝ x y
regularFormulaMax≡max =
  CRExt.lipschitzExtensionality₂
    regularFormulaMax CRLattice.maxℝ
    formulaMax-isLipschitz₁ formulaMax-isLipschitz₂
    max-isLipschitz₁ max-isLipschitz₂
    (λ p q → formulaMax-rat p q ∙ sym (CRLattice.max-rat p q))


fromRegular-presFormulaMax : ∀ x y →
  Comparison.fromRegular
    (regularFormulaMax x y) ≡
  Comparison.fromRegular x RealLattice.⊔ℝ
    Comparison.fromRegular y
fromRegular-presFormulaMax x y =
    ComparisonAlgebra.fromRegular-presRationalScalar
      RealLattice.rationalHalf (regularMaxBody x y)
  ∙ cong (RealLattice.rationalHalf RealScalar.⋆_)
      (ComparisonAlgebra.fromRegular-presAddition
        (CRAdd._+_ x y) (CRAbs.absℝ (CRAdd._+_ x (CRNeg.- y))))
  ∙ cong (RealLattice.rationalHalf RealScalar.⋆_)
      (cong₂ RealAdd._+_
        (ComparisonAlgebra.fromRegular-presAddition x y)
        (ComparisonAlgebra.fromRegular-presAbsoluteValue
          (CRAdd._+_ x (CRNeg.- y))
        ∙ cong RealAbs.absℝ
            (ComparisonAlgebra.fromRegular-presAddition
              x (CRNeg.- y)
            ∙ cong (RealAdd._+_
                (Comparison.fromRegular x))
                (ComparisonAlgebra.fromRegular-presNegation y))))


fromRegular-presMax : ∀ x y →
  Comparison.fromRegular (CRLattice.maxℝ x y) ≡
  Comparison.fromRegular x RealLattice.⊔ℝ
    Comparison.fromRegular y
fromRegular-presMax x y =
    cong Comparison.fromRegular
      (sym (regularFormulaMax≡max x y))
  ∙ fromRegular-presFormulaMax x y


fromRegular-presMin : ∀ x y →
  Comparison.fromRegular (CRLattice.minℝ x y) ≡
  Comparison.fromRegular x RealLattice.⊓ℝ
    Comparison.fromRegular y
fromRegular-presMin x y =
    ComparisonAlgebra.fromRegular-presNegation
      (CRLattice.maxℝ (CRNeg.- x) (CRNeg.- y))
  ∙ cong RealNeg.-_
      (fromRegular-presMax (CRNeg.- x) (CRNeg.- y))
  ∙ cong RealNeg.-_
      (cong₂ RealLattice._⊔ℝ_
        (ComparisonAlgebra.fromRegular-presNegation x)
        (ComparisonAlgebra.fromRegular-presNegation y))


fromRegular-pres≤ : ∀ x y →
  x CROrder.≤ℝ y →
  Comparison.fromRegular x RealLattice.≤ℝ
    Comparison.fromRegular y
fromRegular-pres≤ x y x≤y =
    sym (fromRegular-presMax x y)
  ∙ cong Comparison.fromRegular
      (CROrder.maxOf≤ x y x≤y)
