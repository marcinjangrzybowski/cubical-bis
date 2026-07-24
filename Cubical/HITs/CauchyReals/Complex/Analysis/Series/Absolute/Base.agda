module Cubical.HITs.CauchyReals.Complex.Analysis.Series.Absolute.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base using
  (Seq; seqΣ; IsCauchySequence')

open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Analysis.Sequence


modulusTerms : ComplexSequence → Seq
modulusTerms terms n = modulus (terms n)


absolutePartialSum : ComplexSequence → Seq
absolutePartialSum terms = seqΣ (λ n → modulus (terms n))


IsAbsolutelyConvergentSeriesℂ : ComplexSequence → Type₀
IsAbsolutelyConvergentSeriesℂ terms =
  IsCauchySequence' (absolutePartialSum terms)
