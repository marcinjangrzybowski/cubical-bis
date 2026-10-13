module Cubical.Analysis.Complex.Conjugation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.CommRing using (ℝCommRing)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
import Cubical.Analysis.Complex.Algebra.Conjugation as ConjugationDefinition

open ConjugationDefinition.Conjugation ℝCommRing public
  using (conjugate; conjugate-involutive; conjugate-pres+;
    conjugate-pres·; conjugate-pres1)

conjugateHom : CommRingHom ℂCommRing ℂCommRing
conjugateHom = conjugate ,
  makeIsCommRingHom conjugate-pres1 conjugate-pres+ conjugate-pres·

conjugateEquiv : ℂ ≃ ℂ
conjugateEquiv = isoToEquiv
  (iso conjugate conjugate conjugate-involutive conjugate-involutive)
