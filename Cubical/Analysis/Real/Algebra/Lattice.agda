module Cubical.Analysis.Real.Algebra.Lattice where

open import Cubical.Analysis.Real.Algebra.Lattice.Base public
  using
    ( maxℝ
    ; max-rat
    ; max-isNonExpanding₁
    ; max-isNonExpanding₂
    ; max-isContinuous₁
    ; max-isContinuous₂
    ; max-pres∼₁
    ; max-pres∼₂
    ; minℝ
    ; min-rat
    ; min-isNonExpanding₁
    ; min-isNonExpanding₂
    ; min-isContinuous₁
    ; min-isContinuous₂
    ; maxOfContinuousIsContinuous
    ; minOfContinuousIsContinuous
    )
open import Cubical.Analysis.Real.Algebra.Lattice.Laws public
  using
    ( maxComm
    ; maxAssoc
    ; maxIdem
    ; minComm
    ; minAssoc
    ; minIdem
    ; maxAbsorbMin
    ; minAbsorbMax
    )
