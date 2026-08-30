module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Laws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Rationals.Inverse using (_⁻¹₊)
import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Limits
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Bounded
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Compatibility

open PositiveRationals


clampedReciprocalProduct : ℚ₊ → Real.ℝ → Real.ℝ
clampedReciprocalProduct η x =
  positiveClamp η x Mul.· boundedReciprocalℝ η (positiveClamp η x)


private
  lim-cong : ∀ {x y : ℕ → Real.ℝ}
    (gx : Real.Base.IsCauchySequence x)
    (gy : Real.Base.IsCauchySequence y) →
    x ≡ y → Real.Base.lim x gx ≡ Real.Base.lim y gy
  lim-cong {x} {y} gx gy p =
    cong (λ z → Real.Base.lim (fst z) (snd z))
      (Σ≡Prop Real.Base.isPropIsCauchySequence p)


  clampedReciprocalProduct-ι : ∀ η q →
    clampedReciprocalProduct η (Real.ιℚ q) ≡ Real.ιℚ 1
  clampedReciprocalProduct-ι η q =
      cong₂ Mul._·_
        (positiveClamp-ι η q)
        (cong (boundedReciprocalℝ η) (positiveClamp-ι η q)
        ∙ boundedReciprocal-ι η (fst r))
    ∙ Mul.mul-ι-ι (fst r) (boundedReciprocalℚ η (fst r))
    ∙ cong Real.ιℚ
        (cong (fst r ℚ.·_)
          (boundedReciprocalℚAbove
            η (fst r) (snd r) (ℚ.≤max (fst η) q))
        ∙ ℚInv.x·invℚ₊[x] r)
    where
    r : ℚ₊
    r = clampedPositive η q


  clampedReciprocalProduct-law-elim : ∀ η →
    Real.Base.ElimCompletion-Prop
      (λ x → clampedReciprocalProduct η x ≡ Real.ιℚ 1)
  clampedReciprocalProduct-law-elim η
    .Real.Base.ElimCompletion-Prop.ιA q =
      clampedReciprocalProduct-ι η q
  clampedReciprocalProduct-law-elim η
    .Real.Base.ElimCompletion-Prop.limA x gx IH =
      cong₂ Mul._·_
        (positiveClamp-lim η x gx)
        (cong (boundedReciprocalℝ η) (positiveClamp-lim η x gx)
        ∙ boundedReciprocal-lim η clampedSequence clampedWitness)
    ∙ Mul.mul-lim-lim
        clampedSequence clampedWitness
        reciprocalSequence reciprocalWitness
    ∙ lim-cong productWitness
        (constantIsCauchySequence (Real.ιℚ 1))
        (funExt IH)
    ∙ lim-constant (Real.ιℚ 1)
        (constantIsCauchySequence (Real.ιℚ 1))
    where
    clampedSequence : ℕ → Real.ℝ
    clampedSequence = positiveClamp η ∘ x

    clampedWitness : Real.Base.IsCauchySequence clampedSequence
    clampedWitness = positiveClamp-seqWitness η gx

    reciprocalSequence : ℕ → Real.ℝ
    reciprocalSequence = boundedReciprocalℝ η ∘ clampedSequence

    reciprocalWitness : Real.Base.IsCauchySequence reciprocalSequence
    reciprocalWitness = boundedReciprocal-seqWitness η clampedWitness

    productWitness : Real.Base.IsCauchySequence
      (λ n → clampedSequence n Mul.· reciprocalSequence n)
    productWitness =
      Mul.mul-diagonalIsCauchySequence clampedWitness reciprocalWitness
  clampedReciprocalProduct-law-elim η
    .Real.Base.ElimCompletion-Prop.isPropA x =
      Real.Base.isSetCompletion _ _


clampedReciprocalLaw : ∀ η x →
  positiveClamp η x Mul.· boundedReciprocalℝ η (positiveClamp η x)
    ≡ Real.ιℚ 1
clampedReciprocalLaw η =
  Real.Base.ElimCompletion-Prop.go (clampedReciprocalProduct-law-elim η)


boundedReciprocalLaw : ∀ η x →
  Real.ιℚ (fst η) ≤ℝ x →
  x Mul.· boundedReciprocalℝ η x ≡ Real.ιℚ 1
boundedReciprocalLaw η x η≤x =
    sym
      (cong₂ Mul._·_
        clampFix (cong (boundedReciprocalℝ η) clampFix))
  ∙ clampedReciprocalLaw η x
  where
  clampFix : positiveClamp η x ≡ x
  clampFix = η≤x
