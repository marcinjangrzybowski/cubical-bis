module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Laws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base
  as Scalar


private
  lim-cong : ∀ {x y : ℕ → Real.ℝ}
    (gx : Real.Base.IsCauchySequence x) (gy : Real.Base.IsCauchySequence y) →
    x ≡ y → Real.Base.lim x gx ≡ Real.Base.lim y gy
  lim-cong {x} {y} gx gy p =
    cong (λ z → Real.Base.lim (fst z) (snd z))
      (Σ≡Prop Real.Base.isPropIsCauchySequence p)


private
  scalar-assoc-elim : ∀ c d → Real.Base.ElimCompletion-Prop
    (λ x → (c ℚR.· d) Scalar.⋆ x ≡ c Scalar.⋆ (d Scalar.⋆ x))
  scalar-assoc-elim c d .Real.Base.ElimCompletion-Prop.ιA q =
    cong Real.ιℚ ℚ!
  scalar-assoc-elim c d .Real.Base.ElimCompletion-Prop.limA x gx IH =
    lim-cong _ _ (funExt IH)
  scalar-assoc-elim c d .Real.Base.ElimCompletion-Prop.isPropA x =
    Real.Base.isSetCompletion _ _

scalar-assoc : ∀ c d x →
  (c ℚR.· d) Scalar.⋆ x ≡ c Scalar.⋆ (d Scalar.⋆ x)
scalar-assoc c d = Real.Base.ElimCompletion-Prop.go (scalar-assoc-elim c d)


private
  scalar-id-elim : Real.Base.ElimCompletion-Prop
    (λ x → 1 Scalar.⋆ x ≡ x)
  scalar-id-elim .Real.Base.ElimCompletion-Prop.ιA q =
    cong Real.ιℚ ℚ!
  scalar-id-elim .Real.Base.ElimCompletion-Prop.limA x gx IH =
    lim-cong _ _ (funExt IH)
  scalar-id-elim .Real.Base.ElimCompletion-Prop.isPropA x =
    Real.Base.isSetCompletion _ _

scalar-id : ∀ x → 1 Scalar.⋆ x ≡ x
scalar-id = Real.Base.ElimCompletion-Prop.go scalar-id-elim


private
  scalar-dist-left-elim : ∀ c d → Real.Base.ElimCompletion-Prop
    (λ x →
      (c ℚR.+ d) Scalar.⋆ x ≡
      (c Scalar.⋆ x) Add.+ (d Scalar.⋆ x))
  scalar-dist-left-elim c d .Real.Base.ElimCompletion-Prop.ιA q =
    cong Real.ιℚ ℚ!
  scalar-dist-left-elim c d .Real.Base.ElimCompletion-Prop.limA x gx IH =
    lim-cong _ _ (funExt IH)
    ∙ sym (Add.add-lim-lim _ _ _ _)
  scalar-dist-left-elim c d .Real.Base.ElimCompletion-Prop.isPropA x =
    Real.Base.isSetCompletion _ _

scalar-dist-left : ∀ c d x →
  (c ℚR.+ d) Scalar.⋆ x ≡
  (c Scalar.⋆ x) Add.+ (d Scalar.⋆ x)
scalar-dist-left c d =
  Real.Base.ElimCompletion-Prop.go (scalar-dist-left-elim c d)


-- Distribution over addition needs both constructor arguments.  The two
-- limit/limit branches use the synchronized computation rule for addition.

private
  scalar-dist-right-rational-left : ∀ c p →
    Real.Base.ElimCompletion-Prop
      (λ y → c Scalar.⋆ (Real.ιℚ p Add.+ y) ≡
        (c Scalar.⋆ Real.ιℚ p) Add.+ (c Scalar.⋆ y))
  scalar-dist-right-rational-left c p
    .Real.Base.ElimCompletion-Prop.ιA q =
      cong Real.ιℚ ℚ!
  scalar-dist-right-rational-left c p
    .Real.Base.ElimCompletion-Prop.limA y gy IH =
      lim-cong _ _ (funExt IH)
  scalar-dist-right-rational-left c p
    .Real.Base.ElimCompletion-Prop.isPropA y =
      Real.Base.isSetCompletion _ _

  scalar-dist-right-limit-left : ∀ c x gx →
    (∀ n y → c Scalar.⋆ (x n Add.+ y) ≡
      (c Scalar.⋆ x n) Add.+ (c Scalar.⋆ y)) →
    Real.Base.ElimCompletion-Prop
      (λ y → c Scalar.⋆ (Real.Base.lim x gx Add.+ y) ≡
        (c Scalar.⋆ Real.Base.lim x gx) Add.+ (c Scalar.⋆ y))
  scalar-dist-right-limit-left c x gx IH
    .Real.Base.ElimCompletion-Prop.ιA q =
      lim-cong _ _ (funExt λ n → IH n (Real.ιℚ q))
  scalar-dist-right-limit-left c x gx IH
    .Real.Base.ElimCompletion-Prop.limA y gy JH =
      lim-cong _ _ (funExt λ n → IH n (Real.Base.lim y gy))
  scalar-dist-right-limit-left c x gx IH
    .Real.Base.ElimCompletion-Prop.isPropA y =
      Real.Base.isSetCompletion _ _

  scalar-dist-right-elim : ∀ c → Real.Base.ElimCompletion-Prop
    (λ x → ∀ y → c Scalar.⋆ (x Add.+ y) ≡
      (c Scalar.⋆ x) Add.+ (c Scalar.⋆ y))
  scalar-dist-right-elim c .Real.Base.ElimCompletion-Prop.ιA p =
    Real.Base.ElimCompletion-Prop.go (scalar-dist-right-rational-left c p)
  scalar-dist-right-elim c .Real.Base.ElimCompletion-Prop.limA x gx IH =
    Real.Base.ElimCompletion-Prop.go
      (scalar-dist-right-limit-left c x gx IH)
  scalar-dist-right-elim c .Real.Base.ElimCompletion-Prop.isPropA x =
    isPropΠ λ y → Real.Base.isSetCompletion _ _

scalar-dist-right : ∀ c x y →
  c Scalar.⋆ (x Add.+ y) ≡
  (c Scalar.⋆ x) Add.+ (c Scalar.⋆ y)
scalar-dist-right c =
  Real.Base.ElimCompletion-Prop.go (scalar-dist-right-elim c)
