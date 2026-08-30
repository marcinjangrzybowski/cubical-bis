module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Continuity where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚData
import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Properties as ℚP
open import Cubical.Data.Rationals.Inverse

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
  using (mul-comm)
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
  using (add-monotone)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
  using (abs-mul ; mul-preserves≤-left-nonnegative)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Multiplication
  using (mul-preserves≪-right-positive)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order
  using (closeness→absDifference< ; absDifference<→closeness ; close→upperBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


-- Multiplication by a real bounded by B is B-Lipschitz.  The bound is local
-- data; no global boundedness choice is built into multiplication.

mulIsLipschitzRightAtBound : ∀ B y →
  Abs.absℝ y ≤ℝ Real.ιℚ (fst B) →
  IsLipschitzWith
    (snd Real.ℝPremetricSpace) (λ x → x Mul.· y)
    (snd Real.ℝPremetricSpace) B
mulIsLipschitzRightAtBound B y absy≤B
  .IsLipschitzWith.pres≈ x x' ε x≈x' =
  absDifference<→closeness
    (x Mul.· y) (x' Mul.· y) (B ·₊ ε)
    (subst (_<ℝ Real.ιℚ (fst (B ·₊ ε)))
      (sym outputAbsPath) productStrict)
  where
  absDifferenceStrict :
    Abs.absℝ (x Group.- x') <ℝ Real.ιℚ (fst ε)
  absDifferenceStrict =
    closeness→absDifference< x x' ε x≈x'

  product≤ :
    Abs.absℝ (x Group.- x') Mul.· Abs.absℝ y ≤ℝ
    Abs.absℝ (x Group.- x') Mul.· Real.ιℚ (fst B)
  product≤ =
    mul-preserves≤-left-nonnegative
      (Abs.absℝ y) (Real.ιℚ (fst B))
      (Abs.absℝ (x Group.- x')) absy≤B
      (zero≤abs (x Group.- x'))

  productStrictBeforePath :
    Abs.absℝ (x Group.- x') Mul.· Real.ιℚ (fst B) <ℝ
    Real.ιℚ (fst ε) Mul.· Real.ιℚ (fst B)
  productStrictBeforePath =
    mul-preserves≪-right-positive
      (Abs.absℝ (x Group.- x')) (Real.ιℚ (fst ε))
      (Real.ιℚ (fst B)) absDifferenceStrict
      (<ℚ→<ℝ 0 (fst B) (snd B))

  radiusPath :
    Real.ιℚ (fst ε) Mul.· Real.ιℚ (fst B) ≡
    Real.ιℚ (fst (B ·₊ ε))
  radiusPath =
    Mul.mul-ι-ι (fst ε) (fst B)
    ∙ cong Real.ιℚ (ℚP.·Comm (fst ε) (fst B))

  productStrict :
    Abs.absℝ (x Group.- x') Mul.· Abs.absℝ y <ℝ
    Real.ιℚ (fst (B ·₊ ε))
  productStrict =
    subst
      (Abs.absℝ (x Group.- x') Mul.· Abs.absℝ y <ℝ_)
      radiusPath
      (≤<ℝ-trans
        (Abs.absℝ (x Group.- x') Mul.· Abs.absℝ y)
        (Abs.absℝ (x Group.- x') Mul.· Real.ιℚ (fst B))
        (Real.ιℚ (fst ε) Mul.· Real.ιℚ (fst B))
        product≤ productStrictBeforePath)

  outputAbsPath :
    Abs.absℝ ((x Mul.· y) Group.- (x' Mul.· y)) ≡
    Abs.absℝ (x Group.- x') Mul.· Abs.absℝ y
  outputAbsPath =
    cong Abs.absℝ (sym (ℝRing.·DistL- x x' y))
    ∙ abs-mul (x Group.- x') y


mulIsLipschitzLeftAtBound : ∀ B x →
  Abs.absℝ x ≤ℝ Real.ιℚ (fst B) →
  IsLipschitzWith
    (snd Real.ℝPremetricSpace) (x Mul.·_)
    (snd Real.ℝPremetricSpace) B
mulIsLipschitzLeftAtBound B x absx≤B
  .IsLipschitzWith.pres≈ y y' ε y≈y' =
  subst2 (Real.Base._≈ᶜ[ B ·₊ ε ]_)
    (mul-comm y x) (mul-comm y' x)
    (mulIsLipschitzRightAtBound B x absx≤B
      .IsLipschitzWith.pres≈ y y' ε y≈y')


-- Joint continuity uses one merely existing local rational bound at the
-- base point.  Because continuity is proposition-valued, that finite bound
-- can be opened and discarded locally.

mulOfContinuousIsContinuous : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A)
  (f g : A → Real.ℝ) →
  isContinuous source f (snd Real.ℝPremetricSpace) →
  isContinuous source g (snd Real.ℝPremetricSpace) →
  isContinuous source (λ x → f x Mul.· g x)
    (snd Real.ℝPremetricSpace)
mulOfContinuousIsContinuous source f g f-cont g-cont x
  .IsContinuousAt.pres≈ ε = do
  (B , absfx≤B , absgx≤B) ← ∃jointRationalBound (f x) (g x)
  let C = B +₊ B
  (δf , f-close) ←
    f-cont x .IsContinuousAt.pres≈ ((ε /2₊) ₊／₊ B)
  (δB , f-bounded-close) ←
    f-cont x .IsContinuousAt.pres≈ B
  (δg , g-close) ←
    g-cont x .IsContinuousAt.pres≈ ((ε /2₊) ₊／₊ C)
  let δ = min₊ δf (min₊ δB δg)
  return
    ( δ
    , λ y x≈y →
      let
        x≈δfy = PremetricStr.isMonotone≈≤ source x y δ δf
          (min₊≤L δf (min₊ δB δg)) x≈y

        x≈δBy = PremetricStr.isMonotone≈≤ source x y δ δB
          (ℚ.isTrans≤ _ _ _
            (min₊≤R δf (min₊ δB δg))
            (min₊≤L δB δg)) x≈y

        x≈δgy = PremetricStr.isMonotone≈≤ source x y δ δg
          (ℚ.isTrans≤ _ _ _
            (min₊≤R δf (min₊ δB δg))
            (min₊≤R δB δg)) x≈y

        fx≈fy = f-close y x≈δfy
        fx≈Bfy = f-bounded-close y x≈δBy
        gx≈gy = g-close y x≈δgy

        absfy≤absfx+B :
          Abs.absℝ (f y) ≤ℝ
          Abs.absℝ (f x) Add.+ Real.ιℚ (fst B)
        absfy≤absfx+B =
          close→upperBound (Abs.absℝ (f y)) (Abs.absℝ (f x)) B
            (Real.Base.sym≈ᶜ
              (Abs.absℝ (f x)) (Abs.absℝ (f y)) B
              (Abs.absℝ-pres≈ (f x) (f y) B fx≈Bfy))

        absfx+B≤C :
          Abs.absℝ (f x) Add.+ Real.ιℚ (fst B) ≤ℝ
          Real.ιℚ (fst C)
        absfx+B≤C =
          subst
            (Abs.absℝ (f x) Add.+ Real.ιℚ (fst B) ≤ℝ_)
            (Add.add-ι-ι (fst B) (fst B))
            (add-monotone
              (Abs.absℝ (f x)) (Real.ιℚ (fst B))
              (Real.ιℚ (fst B)) (Real.ιℚ (fst B))
              absfx≤B (≤ℝ-refl (Real.ιℚ (fst B))))

        absfy≤C : Abs.absℝ (f y) ≤ℝ Real.ιℚ (fst C)
        absfy≤C =
          ≤ℝ-trans (Abs.absℝ (f y))
            (Abs.absℝ (f x) Add.+ Real.ιℚ (fst B))
            (Real.ιℚ (fst C)) absfy≤absfx+B absfx+B≤C

        firstHalf :
          (f x Mul.· g x) Real.Base.≈ᶜ[ ε /2₊ ] (f y Mul.· g x)
        firstHalf =
          subst
            (λ ρ → (f x Mul.· g x) Real.Base.≈ᶜ[ ρ ]
              (f y Mul.· g x))
            (ℚ₊≡ (·／ B (ε /2₊)))
            (mulIsLipschitzRightAtBound B (g x) absgx≤B
              .IsLipschitzWith.pres≈
                (f x) (f y) ((ε /2₊) ₊／₊ B) fx≈fy)

        secondHalf :
          (f y Mul.· g x) Real.Base.≈ᶜ[ ε /2₊ ] (f y Mul.· g y)
        secondHalf =
          subst
            (λ ρ → (f y Mul.· g x) Real.Base.≈ᶜ[ ρ ]
              (f y Mul.· g y))
            (ℚ₊≡ (·／ C (ε /2₊)))
            (mulIsLipschitzLeftAtBound C (f y) absfy≤C
              .IsLipschitzWith.pres≈
                (g x) (g y) ((ε /2₊) ₊／₊ C) gx≈gy)
      in
      subst
        (λ ρ → (f x Mul.· g x) Real.Base.≈ᶜ[ ρ ]
          (f y Mul.· g y))
        (ℚ₊≡ (/2+/2≡id (fst ε)))
        (Real.Approximation.tri≈ᶜ
          (f x Mul.· g x) (f y Mul.· g x) (f y Mul.· g y)
          (ε /2₊) (ε /2₊) firstHalf secondHalf)
    )
