module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.ScalarCompatibility where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base
  as Scalar
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

  rational-left-elim : ∀ c → Real.Base.ElimCompletion-Prop
    (λ x → Real.ιℚ c Mul.· x ≡ c Scalar.⋆ x)
  rational-left-elim c .Real.Base.ElimCompletion-Prop.ιA q = refl
  rational-left-elim c .Real.Base.ElimCompletion-Prop.limA x gx IH =
    lim-cong _ _ (funExt IH)
  rational-left-elim c .Real.Base.ElimCompletion-Prop.isPropA x =
    Real.Base.isSetCompletion _ _


mul-rational-left-as-scalar : ∀ c x →
  Real.ιℚ c Mul.· x ≡ c Scalar.⋆ x
mul-rational-left-as-scalar c =
  Real.Base.ElimCompletion-Prop.go (rational-left-elim c)


mul-rational-right-as-scalar : ∀ x c →
  x Mul.· Real.ιℚ c ≡ c Scalar.⋆ x
mul-rational-right-as-scalar x c =
  mul-comm x (Real.ιℚ c) ∙ mul-rational-left-as-scalar c x
