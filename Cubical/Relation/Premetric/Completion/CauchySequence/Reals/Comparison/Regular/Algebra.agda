module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Rationals.Order.Algebra as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing

open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Relation.Premetric.Instances.Rationals using
  (ℚPremetricSpace)
import Cubical.Relation.Premetric.Completion.Properties.Lift
  as RegularLift

open import Cubical.HITs.CauchyRealsP.Foundation.Closeness as CR
import Cubical.HITs.CauchyRealsP.Foundation.Approximation as CRApprox
import Cubical.HITs.CauchyRealsP.Algebra.Negation as CRNeg
import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue as CRAbs
import Cubical.HITs.CauchyRealsP.Algebra.Order.Base as CROrder
import Cubical.HITs.CauchyRealsP.Algebra.Addition as CRAdd
import Cubical.HITs.CauchyRealsP.Algebra.Multiplication as CRMul
import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Continuity as CRMulCont
import Cubical.HITs.CauchyRealsP.Foundation.UniversalProperty as CRUniversal

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
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Affine
  as RealAffine
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular
  as Comparison
import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CauchyGraph.Binary
  as BinaryDefinition

private
  module B = BinaryDefinition
    ℚPremetricSpace ℚPremetricSpace ℚPremetricSpace

  additionGraph : ℚ → ℚ → Real.ℝ
  additionGraph p q = Real.ιℚ (RealAdd.rationalAddition p q)


regularNegationⁿ : NE[ CR.ℝPremetricSpace , CR.ℝPremetricSpace ]
regularNegationⁿ .fst = CRNeg.-_
regularNegationⁿ .snd = CRNeg.negIsNonExpanding

regularAbsoluteValueⁿ :
  NE[ CR.ℝPremetricSpace , CR.ℝPremetricSpace ]
regularAbsoluteValueⁿ .fst = CRAbs.absℝ
regularAbsoluteValueⁿ .snd = CRAbs.absIsNonExpanding


fromRegular-presNegationⁿ :
  Comparison.fromRegularⁿ ∘NE regularNegationⁿ ≡
  RealNeg.negationⁿ ∘NE Comparison.fromRegularⁿ
fromRegular-presNegationⁿ =
  RegularLift.nonExpanding≡
    ℚPremetricSpace Real.ℝPremetricSpace _ _
    (funExt λ q →
      cong Comparison.fromRegular (CRNeg.neg-rat q)
      ∙ Comparison.fromRegular-rat (ℚR.- q)
      ∙ sym
          (cong RealNeg.-_
            (Comparison.fromRegular-rat q)
          ∙ RealNeg.neg-ι q))

fromRegular-presNegation : ∀ x →
  Comparison.fromRegular (CRNeg.- x) ≡
  RealNeg.- Comparison.fromRegular x
fromRegular-presNegation x =
  funExt⁻ (cong fst fromRegular-presNegationⁿ) x


fromRegular-presAbsoluteValueⁿ :
  Comparison.fromRegularⁿ ∘NE
    regularAbsoluteValueⁿ ≡
  RealAbs.absoluteValueⁿ ∘NE
    Comparison.fromRegularⁿ
fromRegular-presAbsoluteValueⁿ =
  RegularLift.nonExpanding≡
    ℚPremetricSpace Real.ℝPremetricSpace _ _
    (funExt λ q →
      cong Comparison.fromRegular (CRAbs.abs-rat q)
      ∙ Comparison.fromRegular-rat
          (fst RealAbs.rationalAbsoluteValueⁿ q)
      ∙ sym
          (cong RealAbs.absℝ
            (Comparison.fromRegular-rat q)
          ∙ RealAbs.absℝ-ι q))

fromRegular-presAbsoluteValue : ∀ x →
  Comparison.fromRegular (CRAbs.absℝ x) ≡
  RealAbs.absℝ (Comparison.fromRegular x)
fromRegular-presAbsoluteValue x =
  funExt⁻ (cong fst fromRegular-presAbsoluteValueⁿ) x


opaque
 regularAdditionGraph : ∀ x y →
   B.BaseGraphClosure RealAdd.rationalAddition
     (Comparison.fromRegular x)
     (Comparison.fromRegular y)
     (Comparison.fromRegular (CRAdd._+_ x y))
 regularAdditionGraph x y α β γ =
   PT.rec2 squash₁ combine
     (CRApprox.∃ratApprox x leftRadius)
     (CRApprox.∃ratApprox y rightRadius)
   where
   leftRadius rightRadius : ℚ₊
   leftRadius = min₊ α (γ /4₊) /2₊
   rightRadius = min₊ β (γ /4₊) /2₊

   sumRadius<γ : leftRadius +₊ rightRadius <₊ γ
   sumRadius<γ = begin<
     fst (leftRadius +₊ rightRadius)
       <⟨ +Mono< _ _ _ _
            (min/2₊<R α (γ /4₊))
            (min/2₊<R β (γ /4₊)) ⟩
     fst (γ /4₊ +₊ γ /4₊)
       ≡→≤⟨ /4+/4≡/2 (fst γ) ⟩
     fst (γ /2₊)
       <⟨ /2₊<id γ ⟩
     fst γ ◾

   combine :
     (Σ[ p ∈ ℚ ] (CR.rat p CR.∼[ leftRadius ] x)) →
     (Σ[ q ∈ ℚ ] (CR.rat q CR.∼[ rightRadius ] y)) →
     ∥ Σ[ p ∈ ℚ ]
         Σ[ q ∈ ℚ ]
           (Real.ιℚ p Real.Base.≈ᶜ[ α ]
             Comparison.fromRegular x) ×
           (Real.ιℚ q Real.Base.≈ᶜ[ β ]
             Comparison.fromRegular y) ×
           (Real.ιℚ (RealAdd.rationalAddition p q)
             Real.Base.≈ᶜ[ γ ]
             Comparison.fromRegular (CRAdd._+_ x y)) ∥₁
   combine (p , p∼x) (q , q∼y) =
     ∣ p , q , leftClose , rightClose , sumClose ∣₁
     where
     leftClose :
       Real.ιℚ p Real.Base.≈ᶜ[ α ]
         Comparison.fromRegular x
     leftClose =
       Real.Base.isMonotone≈ᶜ< _ _ leftRadius α
         (min/2₊<L α (γ /4₊))
         (subst
           (λ z → z Real.Base.≈ᶜ[ leftRadius ]
             Comparison.fromRegular x)
           (Comparison.fromRegular-rat p)
           (Comparison.fromRegular-pres≈ p∼x))

     rightClose :
       Real.ιℚ q Real.Base.≈ᶜ[ β ]
         Comparison.fromRegular y
     rightClose =
       Real.Base.isMonotone≈ᶜ< _ _ rightRadius β
         (min/2₊<L β (γ /4₊))
         (subst
           (λ z → z Real.Base.≈ᶜ[ rightRadius ]
             Comparison.fromRegular y)
           (Comparison.fromRegular-rat q)
           (Comparison.fromRegular-pres≈ q∼y))

     rationalSumClose :
       CR.rat (p ℚR.+ q) CR.∼[ leftRadius +₊ rightRadius ]
         CRAdd._+_ x y
     rationalSumClose =
       subst
         (λ z → z CR.∼[ leftRadius +₊ rightRadius ]
           CRAdd._+_ x y)
         (CRAdd.rat+rat p q)
         (CRAdd.addPres∼
           (CR.rat p) x (CR.rat q) y
           leftRadius rightRadius p∼x q∼y)

     sumClose :
       Real.ιℚ (RealAdd.rationalAddition p q)
         Real.Base.≈ᶜ[ γ ]
       Comparison.fromRegular (CRAdd._+_ x y)
     sumClose =
       Real.Base.isMonotone≈ᶜ< _ _
         (leftRadius +₊ rightRadius) γ sumRadius<γ
         (subst
           (λ z → z Real.Base.≈ᶜ[ leftRadius +₊ rightRadius ]
             Comparison.fromRegular (CRAdd._+_ x y))
           (Comparison.fromRegular-rat (p ℚR.+ q))
           (Comparison.fromRegular-pres≈
             rationalSumClose))


fromRegular-presAddition : ∀ x y →
  Comparison.fromRegular (CRAdd._+_ x y) ≡
  RealAdd._+_
    (Comparison.fromRegular x)
    (Comparison.fromRegular y)
fromRegular-presAddition x y =
  sym
    (B.graphClosureUnique additionGraph
      RealAdd.rationalAddition-preservesCauchyGraphs
      (Comparison.fromRegular x)
      (Comparison.fromRegular y)
      _ _
      (RealAdd.addition-joint
        (Comparison.fromRegular x)
        (Comparison.fromRegular y))
      (regularAdditionGraph x y))


-- The comparison also preserves the unconditional fragment of
-- multiplication: multiplication by a fixed rational.  Both sides are
-- Lipschitz maps out of the ordinary completion, so rational agreement
-- determines them everywhere.

private
  scalarBoundContains : ∀ c →
    CRAbs.absℝ (CR.rat c) CROrder.≤ℝ
      CR.rat (fst (RealScalar.rationalScalarBound c))
  scalarBoundContains c =
    subst
      (CROrder._≤ℝ CR.rat (fst (RealScalar.rationalScalarBound c)))
      (sym (CRAbs.abs-rat c))
      (CROrder.≤ℚ→≤ℝ (abs c)
        (fst (RealScalar.rationalScalarBound c))
        (ℚ.≤max' 1 (abs c)))

  comparisonAfterRationalScaleIsLipschitz : ∀ c →
    IsLipschitzWith (CR.ℝPremetricSpace .snd)
      (λ x → Comparison.fromRegular
        (CRMul._·_ (CR.rat c) x))
      (Real.ℝPremetricSpace .snd)
      (RealScalar.rationalScalarBound c)
  comparisonAfterRationalScaleIsLipschitz c
    .IsLipschitzWith.pres≈ x y ε x∼y =
      Comparison.fromRegular-pres≈
        (CRMulCont.mulIsLipschitzLAtBound
          (RealScalar.rationalScalarBound c) (CR.rat c)
          (scalarBoundContains c)
          .IsLipschitzWith.pres≈ x y ε x∼y)

  rationalScaleAfterComparisonIsLipschitz : ∀ c →
    IsLipschitzWith (CR.ℝPremetricSpace .snd)
      (λ x → c RealScalar.⋆ Comparison.fromRegular x)
      (Real.ℝPremetricSpace .snd)
      (RealScalar.rationalScalarBound c)
  rationalScaleAfterComparisonIsLipschitz c
    .IsLipschitzWith.pres≈ x y ε x∼y =
      RealScalar.scalar-pres≈ c _ _ ε
        (Comparison.fromRegular-pres≈ x∼y)


fromRegular-presRationalScalar : ∀ c x →
  Comparison.fromRegular
      (CRMul._·_ (CR.rat c) x) ≡
  c RealScalar.⋆ Comparison.fromRegular x
fromRegular-presRationalScalar c =
  funExt⁻
    (CRUniversal.lipschitzExtensionality
      Real.ℝPremetricSpace
      (λ x → Comparison.fromRegular
        (CRMul._·_ (CR.rat c) x))
      (λ x → c RealScalar.⋆ Comparison.fromRegular x)
      ∣ RealScalar.rationalScalarBound c
        , comparisonAfterRationalScaleIsLipschitz c ∣₁
      ∣ RealScalar.rationalScalarBound c
        , rationalScaleAfterComparisonIsLipschitz c ∣₁
      (λ q →
          cong Comparison.fromRegular
            (CRMul.mul-rat c q)
        ∙ Comparison.fromRegular-rat (c ℚR.· q)
        ∙ sym
            (cong (c RealScalar.⋆_)
              (Comparison.fromRegular-rat q)
            ∙ RealScalar.scalar-ι c q)))


fromRegular-presRationalAffine : ∀ c b x →
  Comparison.fromRegular
      (CRAdd._+_ (CRMul._·_ (CR.rat c) x) (CR.rat b)) ≡
  RealAffine.affine c b (Comparison.fromRegular x)
fromRegular-presRationalAffine c b x =
    fromRegular-presAddition
      (CRMul._·_ (CR.rat c) x) (CR.rat b)
  ∙ cong₂ RealAdd._+_
      (fromRegular-presRationalScalar c x)
      (Comparison.fromRegular-rat b)
  ∙ sym (RealAffine.affine-as-add c b
      (Comparison.fromRegular x))


open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular.Multiplication
  public
