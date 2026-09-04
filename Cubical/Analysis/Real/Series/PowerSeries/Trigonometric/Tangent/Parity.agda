module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Parity where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Inverse.Signed
open import Cubical.Analysis.Real.Order.Apartness
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Laws


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)


opaque
  negateTangentDomain : TangentDomain → TangentDomain
  negateTangentDomain point =
    - fst point
    , subst
        (0ℝ #ℝ_)
        (sym (cosℝ-neg (fst point)))
        (snd point)


  negateTangentDomain-coordinate : ∀ point →
    fst (negateTangentDomain point) ≡ - fst point
  negateTangentDomain-coordinate point = refl


  negateTangentDomainNE :
    NE[ TangentDomainPremetricSpace , TangentDomainPremetricSpace ]
  fst negateTangentDomainNE = negateTangentDomain
  IsNonExpanding.pres≈ (snd negateTangentDomainNE) x y ε close =
    neg-isNonExpanding .IsNonExpanding.pres≈
      (fst x) (fst y) ε close


  negateTangentDomain-involutive : ∀ point →
    negateTangentDomain (negateTangentDomain point) ≡ point
  negateTangentDomain-involutive point =
    Σ≡Prop
      (λ x → isProp#ℝ 0ℝ (cosℝ x))
      (negInvol (fst point))


  sinℝ-at-negateTangentDomain : ∀ point →
    sinℝ (fst (negateTangentDomain point))
      ≡ - sinℝ (fst point)
  sinℝ-at-negateTangentDomain point =
    cong sinℝ (negateTangentDomain-coordinate point)
    ∙ sinℝ-neg (fst point)


  cosℝ-at-negateTangentDomain : ∀ point →
    cosℝ (fst (negateTangentDomain point))
      ≡ cosℝ (fst point)
  cosℝ-at-negateTangentDomain point =
    cong cosℝ (negateTangentDomain-coordinate point)
    ∙ cosℝ-neg (fst point)


opaque
  tanℝ-neg : ∀ point →
    tanℝ (negateTangentDomain point) ≡ - tanℝ point
  tanℝ-neg point =
    mul-cancel-right-apart
      (tanℝ (negateTangentDomain point))
      (- tanℝ point)
      (cosℝ (fst (negateTangentDomain point)))
      (snd (negateTangentDomain point))
      ( tanℝ-mul-cosℝ (negateTangentDomain point)
      ∙ sinℝ-at-negateTangentDomain point
      ∙ sym
          ( cong
              ((- tanℝ point) ·_)
              (cosℝ-at-negateTangentDomain point)
          ∙ ℝRing.-DistL· (tanℝ point) (cosℝ (fst point))
          ∙ cong (-_) (tanℝ-mul-cosℝ point)
          )
      )


  secℝ-neg : ∀ point →
    secℝ (negateTangentDomain point) ≡ secℝ point
  secℝ-neg point =
    mul-cancel-right-apart
      (secℝ (negateTangentDomain point))
      (secℝ point)
      (cosℝ (fst (negateTangentDomain point)))
      (snd (negateTangentDomain point))
      ( secℝ-mul-cosℝ (negateTangentDomain point)
      ∙ sym
          ( cong
              (secℝ point ·_)
              (cosℝ-at-negateTangentDomain point)
          ∙ secℝ-mul-cosℝ point
          )
      )
