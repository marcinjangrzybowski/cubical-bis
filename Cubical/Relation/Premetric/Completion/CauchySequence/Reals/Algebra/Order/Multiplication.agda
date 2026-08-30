module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open OrderedCommRingTheory ℚOrderedCommRing

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Negation
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar
  using (zero≤abs)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
  using (mul-comm)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.ScalarCompatibility
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  lim-cong : ∀ {x y : ℕ → Real.ℝ}
    (gx : Real.Base.IsCauchySequence x) (gy : Real.Base.IsCauchySequence y) →
    x ≡ y → Real.Base.lim x gx ≡ Real.Base.lim y gy
  lim-cong {x} {y} gx gy p =
    cong (λ z → Real.Base.lim (fst z) (snd z))
      (Σ≡Prop Real.Base.isPropIsCauchySequence p)

  abs-mul-elim : Real.Base.ElimCompletion-Prop
    (λ x → ∀ y →
      Abs.absℝ (x Mul.· y) ≡
      Abs.absℝ x Mul.· Abs.absℝ y)
  abs-mul-elim .Real.Base.ElimCompletion-Prop.ιA p y =
      cong Abs.absℝ (mul-rational-left-as-scalar p y)
    ∙ abs-scalar p y
    ∙ sym (mul-rational-left-as-scalar (abs p) (Abs.absℝ y))
    ∙ cong (Mul._· Abs.absℝ y) (sym (Abs.absℝ-ι p))
  abs-mul-elim .Real.Base.ElimCompletion-Prop.limA x gx IH y =
    lim-cong _ _ (funExt λ n → IH n y)
  abs-mul-elim .Real.Base.ElimCompletion-Prop.isPropA x =
    isPropΠ λ y → Real.Base.isSetCompletion _ _


abs-mul : ∀ x y →
  Abs.absℝ (x Mul.· y) ≡
  Abs.absℝ x Mul.· Abs.absℝ y
abs-mul = Real.Base.ElimCompletion-Prop.go abs-mul-elim


nonnegative→abs-self : ∀ x →
  Real.ιℚ 0 ≤ℝ x → Abs.absℝ x ≡ x
nonnegative→abs-self x 0≤x =
  ≤ℝ-antisym (Abs.absℝ x) x absx≤x (x≤abs x)
  where
  negx≤0 : (Neg.- x) ≤ℝ Real.ιℚ 0
  negx≤0 = subst ((Neg.- x) ≤ℝ_)
    neg-zero (neg-reverses≤ (Real.ιℚ 0) x 0≤x)

  negx≤x : (Neg.- x) ≤ℝ x
  negx≤x = ≤ℝ-trans (Neg.- x) (Real.ιℚ 0) x negx≤0 0≤x

  absx≤x : Abs.absℝ x ≤ℝ x
  absx≤x = bounds→abs≤ x x (≤ℝ-refl x) negx≤x


abs-self→nonnegative : ∀ x →
  Abs.absℝ x ≡ x → Real.ιℚ 0 ≤ℝ x
abs-self→nonnegative x absx≡x =
  subst (Real.ιℚ 0 ≤ℝ_) absx≡x (zero≤abs x)


mul-nonnegative : ∀ x y →
  Real.ιℚ 0 ≤ℝ x → Real.ιℚ 0 ≤ℝ y →
  Real.ιℚ 0 ≤ℝ (x Mul.· y)
mul-nonnegative x y 0≤x 0≤y =
  abs-self→nonnegative (x Mul.· y)
    (abs-mul x y
      ∙ cong₂ Mul._·_
          (nonnegative→abs-self x 0≤x)
          (nonnegative→abs-self y 0≤y))


mul-preserves≤-right-nonnegative : ∀ x y z →
  x ≤ℝ y → Real.ιℚ 0 ≤ℝ z →
  (x Mul.· z) ≤ℝ (y Mul.· z)
mul-preserves≤-right-nonnegative x y z x≤y 0≤z =
  zero≤difference→≤ (x Mul.· z) (y Mul.· z)
    (subst (Real.ιℚ 0 ≤ℝ_)
      (ℝRing.·DistL- y x z)
      (mul-nonnegative (y Group.- x) z
        (≤→zero≤difference x y x≤y) 0≤z))


mul-preserves≤-left-nonnegative : ∀ x y z →
  x ≤ℝ y → Real.ιℚ 0 ≤ℝ z →
  (z Mul.· x) ≤ℝ (z Mul.· y)
mul-preserves≤-left-nonnegative x y z x≤y 0≤z =
  subst2 _≤ℝ_ (mul-comm x z) (mul-comm y z)
    (mul-preserves≤-right-nonnegative x y z x≤y 0≤z)


mul-monotone-nonnegative : ∀ x x' y y' →
  x ≤ℝ x' → y ≤ℝ y' →
  Real.ιℚ 0 ≤ℝ x → Real.ιℚ 0 ≤ℝ y →
  (x Mul.· y) ≤ℝ (x' Mul.· y')
mul-monotone-nonnegative x x' y y' x≤x' y≤y' 0≤x 0≤y =
  ≤ℝ-trans (x Mul.· y) (x' Mul.· y) (x' Mul.· y')
    (mul-preserves≤-right-nonnegative x x' y x≤x' 0≤y)
    (mul-preserves≤-left-nonnegative y y' x' y≤y'
      (≤ℝ-trans (Real.ιℚ 0) x x' 0≤x x≤x'))
