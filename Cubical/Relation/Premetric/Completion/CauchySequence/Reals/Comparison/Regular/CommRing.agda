module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular.CommRing where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base

open import Cubical.Algebra.CommRing

import Cubical.HITs.CauchyRealsP.Algebra.CommRing as CRRing

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
  as RealRing
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular
  as Comparison
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular.Algebra
  as ComparisonAlgebra
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Comparison.Regular.Multiplication
  as ComparisonMultiplication


fromRegularIsCommRingHom :
  IsCommRingHom
    (snd CRRing.ℝCommRing)
    Comparison.fromRegular
    (snd RealRing.ℝCommRing)
fromRegularIsCommRingHom =
  makeIsCommRingHom
    (Comparison.fromRegular-rat 1)
    ComparisonAlgebra.fromRegular-presAddition
    ComparisonMultiplication.fromRegular-presMultiplication


fromRegularCommRingHom :
  CommRingHom CRRing.ℝCommRing RealRing.ℝCommRing
fromRegularCommRingHom =
  Comparison.fromRegular
  , fromRegularIsCommRingHom
