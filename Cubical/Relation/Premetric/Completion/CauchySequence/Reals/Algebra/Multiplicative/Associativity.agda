module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Sigma

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul


private
  lim-cong : ∀ {x y : ℕ → Real.ℝ}
    (gx : Real.Base.IsCauchySequence x) (gy : Real.Base.IsCauchySequence y) →
    x ≡ y → Real.Base.lim x gx ≡ Real.Base.lim y gy
  lim-cong {x} {y} gx gy p =
    cong (λ z → Real.Base.lim (fst z) (snd z))
      (Σ≡Prop Real.Base.isPropIsCauchySequence p)


-- The synchronized lim/lim rule makes the ordinary three-constructor proof
-- of associativity available without a modulus for multiplication.

private
  inner : ∀ p q → Real.Base.ElimCompletion-Prop
    (λ z →
      Real.ιℚ p Mul.· (Real.ιℚ q Mul.· z) ≡
      (Real.ιℚ p Mul.· Real.ιℚ q) Mul.· z)
  inner p q .Real.Base.ElimCompletion-Prop.ιA r =
    cong Real.ιℚ ℚ!
  inner p q .Real.Base.ElimCompletion-Prop.limA z gz IH =
    lim-cong _ _ (funExt IH)
  inner p q .Real.Base.ElimCompletion-Prop.isPropA z =
    Real.Base.isSetCompletion _ _

  middle : ∀ p → Real.Base.ElimCompletion-Prop
    (λ y → ∀ z →
      Real.ιℚ p Mul.· (y Mul.· z) ≡
      (Real.ιℚ p Mul.· y) Mul.· z)
  middle p .Real.Base.ElimCompletion-Prop.ιA q =
    Real.Base.ElimCompletion-Prop.go (inner p q)
  middle p .Real.Base.ElimCompletion-Prop.limA y gy IH z =
    lim-cong _ _ (funExt λ n → IH n z)
  middle p .Real.Base.ElimCompletion-Prop.isPropA y =
    isPropΠ λ z → Real.Base.isSetCompletion _ _

  outer : Real.Base.ElimCompletion-Prop
    (λ x → ∀ y z →
      x Mul.· (y Mul.· z) ≡ (x Mul.· y) Mul.· z)
  outer .Real.Base.ElimCompletion-Prop.ιA p =
    Real.Base.ElimCompletion-Prop.go (middle p)
  outer .Real.Base.ElimCompletion-Prop.limA x gx IH y z =
    lim-cong _ _ (funExt λ n → IH n y z)
  outer .Real.Base.ElimCompletion-Prop.isPropA x =
    isPropΠ2 λ y z → Real.Base.isSetCompletion _ _


mul-assoc : ∀ x y z →
  x Mul.· (y Mul.· z) ≡ (x Mul.· y) Mul.· z
mul-assoc = Real.Base.ElimCompletion-Prop.go outer
