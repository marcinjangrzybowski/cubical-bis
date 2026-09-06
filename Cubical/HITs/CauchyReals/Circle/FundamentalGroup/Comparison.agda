module Cubical.HITs.CauchyReals.Circle.FundamentalGroup.Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Int.Fast as ℤ using (ℤ; isSetℤ)
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms using (GroupIso; GroupEquiv; IsGroupHom)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.MorphismProperties using
  (makeIsGroupHom; invGroupIso; compGroupIso; GroupIso→GroupEquiv)
open import Cubical.HITs.CauchyReals.Circle.FundamentalGroup.Base public
open import Cubical.HITs.CauchyReals.Circle.FundamentalGroup.Invariance public
open import Cubical.HITs.CauchyReals.Circle.FundamentalGroup.NormalForm public
open import Cubical.HITs.CauchyReals.Circle.FundamentalGroup.Addition public
import Cubical.HITs.CauchyReals.Circle.Homotopy.Algebra as Old
import Cubical.HITs.CauchyReals.Circle.Homotopy.Quotient as Old
import Cubical.HITs.CauchyReals.Circle.Homotopy.Integers as Old
import Cubical.HITs.CauchyReals.Circle.Homotopy.Equivalence as Old

CircleLoopGroup : Group ℓ-zero
CircleLoopGroup = loopGroup

loopClassWinding : LoopClass → ℤ
loopClassWinding = SQ.rec isSetℤ loopWinding
  (λ p q → PT.rec (isSetℤ _ _) (loopWinding-homotopy p q))

-- Keep conversion of quotient expressions from expanding the analytic loop.
opaque
  integerLoopClass : ℤ → LoopClass
  integerLoopClass k = pathClass (integerLoop k)

opaque
  unfolding integerLoopClass
  winding-integerLoopClass : ∀ k → loopClassWinding (integerLoopClass k) ≡ k
  winding-integerLoopClass = integerLoop-winding

private
  opaque
    unfolding integerLoopClass
    loopClassWinding-β : (p : Loop) → loopClassWinding (pathClass p) ≡ loopWinding p
    loopClassWinding-β p = refl

    normal-form-class : (p : Loop) → pathClass p ≡ integerLoopClass (loopWinding p)
    normal-form-class p = SQ.eq/ {R = Homotopic} p (integerLoop (loopWinding p))
      (loop-normal-form p)

integerLoopClass-winding : ∀ c → integerLoopClass (loopClassWinding c) ≡ c
integerLoopClass-winding = SQ.elimProp {A = Loop} {R = Homotopic}
  {P = λ c → integerLoopClass (loopClassWinding c) ≡ c}
  (λ c → SQ.squash/ (integerLoopClass (loopClassWinding c)) c)
  (λ p → cong integerLoopClass (loopClassWinding-β p) ∙ sym (normal-form-class p))

opaque
  unfolding integerLoopClass
  integerLoopClass-add : ∀ k l → integerLoopClass (k ℤ.+ l) ≡
    composeClass (integerLoopClass k) (integerLoopClass l)
  integerLoopClass-add k l = sym
    (homotopy-class≡ (concat-pointwise (integerLoop k) (integerLoop l))
      ∙ cong pathClass (pointwise-integerLoop k l))

ℤ≅circleLoop : GroupIso (AbGroup→Group Old.IntegerAbGroup) CircleLoopGroup
ℤ≅circleLoop = iso integerLoopClass loopClassWinding
  integerLoopClass-winding winding-integerLoopClass , makeIsGroupHom integerLoopClass-add

circleLoop≅ℤ : GroupIso CircleLoopGroup (AbGroup→Group Old.IntegerAbGroup)
circleLoop≅ℤ = invGroupIso ℤ≅circleLoop

-- This is the comparison with the earlier group, including its operation.
-- Forward: a loop goes to the old integer class with the same winding.
-- Inverse: an old class goes to its oriented integer loop.
circleLoop≅circleHomotopy : GroupIso CircleLoopGroup (AbGroup→Group Old.CircleHomotopyAbGroup)
circleLoop≅circleHomotopy = compGroupIso circleLoop≅ℤ Old.ℤ≅circleHomotopy

circleLoop≃circleHomotopy : LoopClass ≃ Old.CircleHomotopyClasses
circleLoop≃circleHomotopy = isoToEquiv (fst circleLoop≅circleHomotopy)

circleLoopGroupEquiv : GroupEquiv CircleLoopGroup (AbGroup→Group Old.CircleHomotopyAbGroup)
circleLoopGroupEquiv = GroupIso→GroupEquiv circleLoop≅circleHomotopy

comparison-winding : ∀ c →
  Old.classWinding (Iso.fun (fst circleLoop≅circleHomotopy) c) ≡ loopClassWinding c
comparison-winding c = Old.winding-integerClass (loopClassWinding c)

comparison-integer : ∀ k →
  Iso.fun (fst circleLoop≅circleHomotopy) (integerLoopClass k) ≡ Old.integerClass k
comparison-integer k = cong Old.integerClass (winding-integerLoopClass k)

loopWinding-concat : (p q : Loop) → loopWinding (concatPath p q) ≡ loopWinding p ℤ.+ loopWinding q
loopWinding-concat p q = IsGroupHom.pres· (snd circleLoop≅ℤ) (pathClass p) (pathClass q)

loopWinding-classifies : (p q : Loop) → Homotopic p q ≃ (loopWinding p ≡ loopWinding q)
loopWinding-classifies p q = propBiimpl→Equiv squash₁ (isSetℤ _ _)
  (PT.rec (isSetℤ _ _) (loopWinding-homotopy p q))
  (λ same → equivFun (class≡≃homotopic p q)
    (sym (integerLoopClass-winding (pathClass p))
      ∙ cong integerLoopClass same ∙ integerLoopClass-winding (pathClass q)))

loopClasses-commute : (p q : LoopClass) → composeClass p q ≡ composeClass q p
loopClasses-commute p q = sym (integerLoopClass-winding (composeClass p q))
  ∙ cong integerLoopClass
      (IsGroupHom.pres· (snd circleLoop≅ℤ) p q ∙ ℤ.+Comm (loopClassWinding p) (loopClassWinding q)
        ∙ sym (IsGroupHom.pres· (snd circleLoop≅ℤ) q p))
  ∙ integerLoopClass-winding (composeClass q p)
