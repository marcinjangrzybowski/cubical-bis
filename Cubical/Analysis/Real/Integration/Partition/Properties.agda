module Cubical.Analysis.Real.Integration.Partition.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.FinData using (Fin)
import Cubical.Data.FinData as FD

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (nonnegativeSub)
open import Cubical.Analysis.Real.FiniteSum.Algebra
open import Cubical.Analysis.Real.Integration.Partition


private
  module ℝSum = Sum (CommRing→Ring ℝCommRing)

open ℝSum using (∑)


module _ {a b : ℝ} (partition : Partition[ a , b ]) where
  open Partition partition

  width : Fin intervalCount → ℝ
  width i = points (FD.suc i) - points (FD.weakenFin i)

  width-nonnegative : ∀ i → 0ℝ ≤ℝ width i
  width-nonnegative i =
    nonnegativeSub
      (points (FD.weakenFin i))
      (points (FD.suc i))
      (monotone i)

  totalWidth : ∑ width ≡ b - a
  totalWidth =
    finiteSumTelescoping points
    ∙ cong₂ _-_ rightEndpoint leftEndpoint
