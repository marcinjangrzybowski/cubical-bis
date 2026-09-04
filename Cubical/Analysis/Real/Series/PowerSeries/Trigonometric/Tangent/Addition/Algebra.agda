module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Algebra where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Inverse.Signed
open import Cubical.Analysis.Real.Order.Apartness


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)


opaque
  tangentAdditionChain3 : (a b c d : ℝ) →
    a ≡ b → b ≡ c → c ≡ d → a ≡ d
  tangentAdditionChain3 a b c d a=b b=c c=d =
    a=b ∙ b=c ∙ c=d


  tangentAdditionChain4 : (a b c d e : ℝ) →
    a ≡ b → b ≡ c → c ≡ d → d ≡ e → a ≡ e
  tangentAdditionChain4 a b c d e
      a=b b=c c=d d=e =
    a=b ∙ b=c ∙ c=d ∙ d=e


  tangentAdditionMultiplyPath : (scale x y : ℝ) →
    x ≡ y → scale · x ≡ scale · y
  tangentAdditionMultiplyPath scale x y =
    cong (scale ·_)


  tangentAdditionInterchange : ∀ a b c d →
    (a · b) · (c · d) ≡ (a · c) · (b · d)
  tangentAdditionInterchange a b c d =
      mulAssoc (a · b) c d
    ∙ cong (_· d) (sym (mulAssoc a b c))
    ∙ cong (λ middle → (a · middle) · d) (mulComm b c)
    ∙ cong (_· d) (mulAssoc a c b)
    ∙ sym (mulAssoc (a · c) b d)


  tangentAdditionCosineFactor : ∀ sx sy cx cy tx ty →
    cx · tx ≡ sx → cy · ty ≡ sy →
    (cx · cy) - (sx · sy)
      ≡
    (cx · cy) · (1ℝ - (tx · ty))
  tangentAdditionCosineFactor
      sx sy cx cy tx ty x-law y-law =
    cong
      (λ value → (cx · cy) - value)
      (cong₂ _·_ (sym x-law) (sym y-law)
      ∙ tangentAdditionInterchange cx tx cy ty)
    ∙ cong
        (_- ((cx · cy) · (tx · ty)))
        (sym (mulIdR (cx · cy)))
    ∙ sym
        (ℝRing.·DistR-
          (cx · cy) 1ℝ (tx · ty))


  tangentAdditionSineFactor : ∀ sx sy cx cy tx ty →
    cx · tx ≡ sx → cy · ty ≡ sy →
    (sx · cy) + (cx · sy)
      ≡
    (cx · cy) · (tx + ty)
  tangentAdditionSineFactor
      sx sy cx cy tx ty x-law y-law =
    cong₂ _+_
      (cong (_· cy) (sym x-law)
      ∙ sym (mulAssoc cx tx cy)
      ∙ cong (cx ·_) (mulComm tx cy)
      ∙ mulAssoc cx cy tx)
      (cong (cx ·_) (sym y-law)
      ∙ mulAssoc cx cy ty)
    ∙ sym (mulDistR (cx · cy) tx ty)


  tangentAdditionCommuteCommonFactor :
    ∀ common tangent denominator →
    common · (tangent · denominator)
      ≡ tangent · (common · denominator)
  tangentAdditionCommuteCommonFactor
      common tangent denominator =
      mulAssoc common tangent denominator
    ∙ cong (_· denominator) (mulComm common tangent)
    ∙ sym (mulAssoc tangent common denominator)


  tangentAdditionCancelCommonLeft : ∀ x y common →
    0ℝ #ℝ common →
    common · x ≡ common · y →
    x ≡ y
  tangentAdditionCancelCommonLeft =
    mul-cancel-left-apart


  tangentAdditionCancelCommonRight : ∀ x y common →
    0ℝ #ℝ common →
    x · common ≡ y · common →
    x ≡ y
  tangentAdditionCancelCommonRight =
    mul-cancel-right-apart
