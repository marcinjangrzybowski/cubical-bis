module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Affine where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings

open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Translation
  as Translation
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base
  as Scalar
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Laws


private
  lim-cong : ∀ {x y : ℕ → Real.ℝ}
    (gx : Real.Base.IsCauchySequence x) (gy : Real.Base.IsCauchySequence y) →
    x ≡ y → Real.Base.lim x gx ≡ Real.Base.lim y gy
  lim-cong {x} {y} gx gy p =
    cong (λ z → Real.Base.lim (fst z) (snd z))
      (Σ≡Prop Real.Base.isPropIsCauchySequence p)

  add-rational-right-elim : ∀ c → Real.Base.ElimCompletion-Prop
    (λ x → x Add.+ Real.ιℚ c ≡ Translation.translate c x)
  add-rational-right-elim c .Real.Base.ElimCompletion-Prop.ιA q = refl
  add-rational-right-elim c .Real.Base.ElimCompletion-Prop.limA x gx IH =
    lim-cong _ _ (funExt IH)
  add-rational-right-elim c .Real.Base.ElimCompletion-Prop.isPropA x =
    Real.Base.isSetCompletion _ _


add-rational-right≡translate : ∀ c x →
  x Add.+ Real.ιℚ c ≡ Translation.translate c x
add-rational-right≡translate c =
  Real.Base.ElimCompletion-Prop.go (add-rational-right-elim c)

add-rational-left≡translate : ∀ c x →
  Real.ιℚ c Add.+ x ≡ Translation.translate c x
add-rational-left≡translate c x =
  add-comm (Real.ιℚ c) x ∙ add-rational-right≡translate c x


-- Affine maps are already available without real multiplication: the slope
-- and intercept are rational parameters fixed before the lift.

affine : ℚ → ℚ → Real.ℝ → Real.ℝ
affine c b x = Translation.translate b (c Scalar.⋆ x)

affine-ι : ∀ c b q →
  affine c b (Real.ιℚ q) ≡ Real.ιℚ ((c ℚR.· q) ℚR.+ b)
affine-ι c b q = refl

affine-as-add : ∀ c b x →
  affine c b x ≡ (c Scalar.⋆ x) Add.+ Real.ιℚ b
affine-as-add c b x =
  sym (add-rational-right≡translate b (c Scalar.⋆ x))

affine-pres≈ : ∀ c b x y ε →
  x Real.Base.≈ᶜ[ ε ] y →
  affine c b x Real.Base.≈ᶜ[
    Scalar.rationalScalarBound c ·₊ ε ] affine c b y
affine-pres≈ c b x y ε x∼y =
  Translation.translate-pres≈ b _ _ _
    (Scalar.scalar-pres≈ c x y ε x∼y)

affine-isLipschitz : ∀ c b →
  isLipschitz
    (Real.ℝPremetricSpace .snd) (affine c b)
    (Real.ℝPremetricSpace .snd)
affine-isLipschitz c b =
  ∣ Scalar.rationalScalarBound c
    , record { pres≈ = affine-pres≈ c b } ∣₁

affine-isContinuous : ∀ c b →
  isContinuous
    (Real.ℝPremetricSpace .snd) (affine c b)
    (Real.ℝPremetricSpace .snd)
affine-isContinuous c b =
  isLipschitz→isContinuous
    (Real.ℝPremetricSpace .snd) (affine c b)
    (Real.ℝPremetricSpace .snd)
    (affine-isLipschitz c b)


affine-identity : ∀ x → affine 1 0 x ≡ x
affine-identity x =
    affine-as-add 1 0 x
  ∙ cong (Add._+ Real.ιℚ 0) (scalar-id x)
  ∙ add-zero-right x

affine-compose : ∀ a b c d x →
  affine a b (affine c d x) ≡
  affine (a ℚR.· c) ((a ℚR.· d) ℚR.+ b) x
affine-compose a b c d x =
    affine-as-add a b (affine c d x)
  ∙ cong (Add._+ Real.ιℚ b)
      (cong (a Scalar.⋆_) (affine-as-add c d x))
  ∙ cong (Add._+ Real.ιℚ b)
      (scalar-dist-right a (c Scalar.⋆ x) (Real.ιℚ d))
  ∙ cong (λ z → (z Add.+ (a Scalar.⋆ Real.ιℚ d)) Add.+ Real.ιℚ b)
      (sym (scalar-assoc a c x))
  ∙ cong (λ z → ((a ℚR.· c) Scalar.⋆ x Add.+ z) Add.+ Real.ιℚ b)
      (Scalar.scalar-ι a d)
  ∙ sym (add-assoc
      ((a ℚR.· c) Scalar.⋆ x) (Real.ιℚ (a ℚR.· d)) (Real.ιℚ b))
  ∙ cong (((a ℚR.· c) Scalar.⋆ x) Add.+_)
      (Add.add-ι-ι (a ℚR.· d) b)
  ∙ sym (affine-as-add
      (a ℚR.· c) ((a ℚR.· d) ℚR.+ b) x)
