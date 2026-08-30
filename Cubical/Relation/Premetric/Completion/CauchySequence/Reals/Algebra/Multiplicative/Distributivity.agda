module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Sigma

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
  using (mul-comm)


private
  lim-cong : ∀ {x y : ℕ → Real.ℝ}
    (gx : Real.Base.IsCauchySequence x) (gy : Real.Base.IsCauchySequence y) →
    x ≡ y → Real.Base.lim x gx ≡ Real.Base.lim y gy
  lim-cong {x} {y} gx gy p =
    cong (λ z → Real.Base.lim (fst z) (snd z))
      (Σ≡Prop Real.Base.isPropIsCauchySequence p)


-- Constructor-by-constructor distribution is available because both binary
-- operations advance two limit inputs synchronously.

private
  inner : ∀ p q → Real.Base.ElimCompletion-Prop
    (λ z →
      Real.ιℚ p Mul.· (Real.ιℚ q Add.+ z) ≡
      (Real.ιℚ p Mul.· Real.ιℚ q) Add.+ (Real.ιℚ p Mul.· z))
  inner p q .Real.Base.ElimCompletion-Prop.ιA r =
    cong Real.ιℚ ℚ!
  inner p q .Real.Base.ElimCompletion-Prop.limA z gz IH =
    lim-cong _ _ (funExt IH)
  inner p q .Real.Base.ElimCompletion-Prop.isPropA z =
    Real.Base.isSetCompletion _ _

  middle : ∀ p → Real.Base.ElimCompletion-Prop
    (λ y → ∀ z →
      Real.ιℚ p Mul.· (y Add.+ z) ≡
      (Real.ιℚ p Mul.· y) Add.+ (Real.ιℚ p Mul.· z))
  middle p .Real.Base.ElimCompletion-Prop.ιA q =
    Real.Base.ElimCompletion-Prop.go (inner p q)
  middle p .Real.Base.ElimCompletion-Prop.limA y gy IH z =
    lim-cong _ _ (funExt λ n → IH n z)
  middle p .Real.Base.ElimCompletion-Prop.isPropA y =
    isPropΠ λ z → Real.Base.isSetCompletion _ _

  outer : Real.Base.ElimCompletion-Prop
    (λ x → ∀ y z →
      x Mul.· (y Add.+ z) ≡
      (x Mul.· y) Add.+ (x Mul.· z))
  outer .Real.Base.ElimCompletion-Prop.ιA p =
    Real.Base.ElimCompletion-Prop.go (middle p)
  outer .Real.Base.ElimCompletion-Prop.limA x gx IH y z =
    lim-cong _ _ (funExt λ n → IH n y z)
    ∙ sym (Add.add-lim-lim _ _ _ _)
  outer .Real.Base.ElimCompletion-Prop.isPropA x =
    isPropΠ2 λ y z → Real.Base.isSetCompletion _ _


mul-distrib-over-add-right : ∀ x y z →
  x Mul.· (y Add.+ z) ≡
  (x Mul.· y) Add.+ (x Mul.· z)
mul-distrib-over-add-right = Real.Base.ElimCompletion-Prop.go outer


mul-distrib-over-add-left : ∀ x y z →
  (x Add.+ y) Mul.· z ≡
  (x Mul.· z) Add.+ (y Mul.· z)
mul-distrib-over-add-left x y z =
  mul-comm (x Add.+ y) z
  ∙ mul-distrib-over-add-right z x y
  ∙ cong₂ Add._+_ (mul-comm z x) (mul-comm z y)
