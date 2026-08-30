module Cubical.Analysis.Real.Algebra.Scalar.Affine where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Algebra.Scalar.Laws

open PositiveRationals


-- Rational affine maps inherit the global Lipschitz bound of their linear
-- part: translation is non-expanding.

affine : ℚ → ℚ → ℝ → ℝ
affine c b x = (c ⋆ x) + rat b

affine-rat : ∀ c b q →
  affine c b (rat q) ≡ rat ((c ℚR.· q) ℚR.+ b)
affine-rat c b q =
  cong (_+ rat b) (scalar-rat c q)
  ∙ rat+rat (c ℚR.· q) b

affine-pres∼ : ∀ c b x y ε →
  x ∼[ ε ] y →
  affine c b x ∼[ rationalScalarBound c ·₊ ε ] affine c b y
affine-pres∼ c b x y ε x∼y =
  add-pres∼₁
    (c ⋆ x) (c ⋆ y) (rat b)
    (rationalScalarBound c ·₊ ε)
    (scalar-pres∼ c x y ε x∼y)

affine-isLipschitzWith : ∀ c b →
  IsLipschitzWith
    (ℝPremetricSpace .snd) (affine c b)
    (ℝPremetricSpace .snd) (rationalScalarBound c)
affine-isLipschitzWith c b .IsLipschitzWith.pres≈ =
  affine-pres∼ c b

affine-isLipschitz : ∀ c b →
  isLipschitz
    (ℝPremetricSpace .snd) (affine c b)
    (ℝPremetricSpace .snd)
affine-isLipschitz c b =
  ∣ rationalScalarBound c , affine-isLipschitzWith c b ∣₁

affine-isUniformlyContinuous : ∀ c b →
  isUniformlyContinuous
    (ℝPremetricSpace .snd) (affine c b)
    (ℝPremetricSpace .snd)
affine-isUniformlyContinuous c b =
  isLipschitz→isUniformlyContinuous
    (ℝPremetricSpace .snd) (affine c b)
    (ℝPremetricSpace .snd)
    (affine-isLipschitz c b)

affine-isContinuous : ∀ c b →
  isContinuous
    (ℝPremetricSpace .snd) (affine c b)
    (ℝPremetricSpace .snd)
affine-isContinuous c b =
  isLipschitz→isContinuous
    (ℝPremetricSpace .snd) (affine c b)
    (ℝPremetricSpace .snd)
    (affine-isLipschitz c b)


affine-identity : ∀ x → affine 1 0 x ≡ x
affine-identity x =
  cong (_+ rat 0) (scalar-id x)
  ∙ addIdR x

affine-compose : ∀ a b c d x →
  affine a b (affine c d x) ≡
  affine (a ℚR.· c) ((a ℚR.· d) ℚR.+ b) x
affine-compose a b c d x =
  cong (_+ rat b)
    (scalar-dist-right a (c ⋆ x) (rat d))
  ∙ cong (λ z → (z + (a ⋆ rat d)) + rat b)
      (sym (scalar-assoc a c x))
  ∙ cong (λ z → (((a ℚR.· c) ⋆ x) + z) + rat b)
      (scalar-rat a d)
  ∙ sym (addAssoc
      ((a ℚR.· c) ⋆ x) (rat (a ℚR.· d)) (rat b))
  ∙ cong (((a ℚR.· c) ⋆ x) +_)
      (rat+rat (a ℚR.· d) b)
