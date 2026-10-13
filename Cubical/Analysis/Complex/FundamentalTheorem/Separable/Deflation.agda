module Cubical.Analysis.Complex.FundamentalTheorem.Separable.Deflation where

open import Cubical.Analysis.Complex.Algebra using (ℂCommRing)
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Basic using (SeparableDeflation)
import Cubical.Analysis.Complex.FundamentalTheorem.Separable.DeflationAlgebra as D

separableDeflation : SeparableDeflation
separableDeflation n = D.Deflation.deflateCertificate ℂCommRing
