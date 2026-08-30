module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚO
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Sigma

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open OrderedCommRingTheory ℚOrderedCommRing

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base
  as Scalar
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition


private
  lim-cong : ∀ {x y : ℕ → Real.ℝ}
    (gx : Real.Base.IsCauchySequence x) (gy : Real.Base.IsCauchySequence y) →
    x ≡ y → Real.Base.lim x gx ≡ Real.Base.lim y gy
  lim-cong {x} {y} gx gy p =
    cong (λ z → Real.Base.lim (fst z) (snd z))
      (Σ≡Prop Real.Base.isPropIsCauchySequence p)

  abs-scalar-elim : ∀ c → Real.Base.ElimCompletion-Prop
    (λ x → Abs.absℝ (c Scalar.⋆ x) ≡
      abs c Scalar.⋆ Abs.absℝ x)
  abs-scalar-elim c .Real.Base.ElimCompletion-Prop.ιA p =
    cong Real.ιℚ (sym (abs·abs c p))
  abs-scalar-elim c .Real.Base.ElimCompletion-Prop.limA x gx IH =
      cong Abs.absℝ (Scalar.scalar-lim c x gx)
    ∙ Abs.absℝ-lim (Scalar._⋆_ c ∘ x) (Scalar.scalar-seqWitness c gx)
    ∙ lim-cong _ _ (funExt IH)
    ∙ sym (Scalar.scalar-lim (abs c)
        (Abs.absℝ ∘ x) (Abs.absℝ-seqWitness gx))
    ∙ cong (abs c Scalar.⋆_) (sym (Abs.absℝ-lim x gx))
  abs-scalar-elim c .Real.Base.ElimCompletion-Prop.isPropA x =
    Real.Base.isSetCompletion _ _


abs-scalar : ∀ c x →
  Abs.absℝ (c Scalar.⋆ x) ≡ abs c Scalar.⋆ Abs.absℝ x
abs-scalar c = Real.Base.ElimCompletion-Prop.go (abs-scalar-elim c)


private
  twoNonnegative : 0 ℚO.≤ 2
  twoNonnegative =
    subst (0 ℚO.≤_) ℚ!
      (NonNegativeRationals.0≤+Closed 1 1 0≤1 0≤1)

  double-as-scalar : ∀ x →
    x Add.+ x ≡ 2 Scalar.⋆ x
  double-as-scalar x =
      cong₂ Add._+_ (sym (scalar-id x)) (sym (scalar-id x))
    ∙ sym (scalar-dist-left 1 1 x)
    ∙ cong (Scalar._⋆ x) ℚ!

  max-with-neg-as-abs : ∀ x →
    x ⊔ℝ (Neg.- x) ≡ Abs.absℝ x
  max-with-neg-as-abs x =
      cong (rationalHalf Scalar.⋆_)
        (cong₂ Add._+_
          (add-inverse-right x)
          (cong Abs.absℝ
            (cong (x Add.+_) (Neg.neg-involutive x)))
        ∙ add-zero-left (Abs.absℝ (x Add.+ x))
        ∙ cong Abs.absℝ (double-as-scalar x)
        ∙ abs-scalar 2 x
        ∙ cong (Scalar._⋆ Abs.absℝ x)
            (0≤→abs≡id 2 twoNonnegative))
    ∙ sym (scalar-assoc rationalHalf 2 (Abs.absℝ x))
    ∙ cong (Scalar._⋆ Abs.absℝ x) ℚ!
    ∙ scalar-id (Abs.absℝ x)


abs-as-max : ∀ x → Abs.absℝ x ≡ x ⊔ℝ (Neg.- x)
abs-as-max x = sym (max-with-neg-as-abs x)

x≤abs : ∀ x → x ≤ℝ Abs.absℝ x
x≤abs x =
  subst (x ≤ℝ_) (sym (abs-as-max x))
    (max-upper-left x (Neg.- x))

neg-x≤abs : ∀ x → (Neg.- x) ≤ℝ Abs.absℝ x
neg-x≤abs x =
  subst ((Neg.- x) ≤ℝ_) (sym (abs-as-max x))
    (max-upper-right x (Neg.- x))

abs≤→bounds : ∀ x y →
  Abs.absℝ x ≤ℝ y → (x ≤ℝ y) × ((Neg.- x) ≤ℝ y)
abs≤→bounds x y abs≤y =
  ≤ℝ-trans x (Abs.absℝ x) y (x≤abs x) abs≤y ,
  ≤ℝ-trans (Neg.- x) (Abs.absℝ x) y (neg-x≤abs x) abs≤y

bounds→abs≤ : ∀ x y →
  x ≤ℝ y → (Neg.- x) ≤ℝ y → Abs.absℝ x ≤ℝ y
bounds→abs≤ x y x≤y neg-x≤y =
  subst (_≤ℝ y) (sym (abs-as-max x))
    (max-least x (Neg.- x) y x≤y neg-x≤y)

add-monotone : ∀ x x' y y' →
  x ≤ℝ x' → y ≤ℝ y' →
  (x Add.+ y) ≤ℝ (x' Add.+ y')
add-monotone x x' y y' x≤x' y≤y' =
  ≤ℝ-trans (x Add.+ y) (x' Add.+ y) (x' Add.+ y')
    (add-preserves≤-right x x' y x≤x')
    (add-preserves≤-left y y' x' y≤y')

abs-triangle : ∀ x y →
  Abs.absℝ (x Add.+ y) ≤ℝ
  (Abs.absℝ x Add.+ Abs.absℝ y)
abs-triangle x y =
  bounds→abs≤ (x Add.+ y)
    (Abs.absℝ x Add.+ Abs.absℝ y)
    (add-monotone x (Abs.absℝ x) y (Abs.absℝ y)
      (x≤abs x) (x≤abs y))
    (subst (_≤ℝ (Abs.absℝ x Add.+ Abs.absℝ y))
      (sym (neg-add x y))
      (add-monotone (Neg.- x) (Abs.absℝ x)
        (Neg.- y) (Abs.absℝ y)
        (neg-x≤abs x) (neg-x≤abs y)))

abs-eq-zero→eq-zero : ∀ x →
  Abs.absℝ x ≡ Real.ιℚ 0 → x ≡ Real.ιℚ 0
abs-eq-zero→eq-zero x absx≡0 =
  ≤ℝ-antisym x (Real.ιℚ 0) x≤0 0≤x
  where
  x≤0 : x ≤ℝ Real.ιℚ 0
  x≤0 = subst (x ≤ℝ_) absx≡0 (x≤abs x)

  neg-x≤0 : (Neg.- x) ≤ℝ Real.ιℚ 0
  neg-x≤0 = subst ((Neg.- x) ≤ℝ_) absx≡0 (neg-x≤abs x)

  0≤x : Real.ιℚ 0 ≤ℝ x
  0≤x = subst2 _≤ℝ_
    (add-inverse-left x) (add-zero-left x)
    (add-preserves≤-right (Neg.- x) (Real.ιℚ 0) x neg-x≤0)

eq-zero→abs-eq-zero : ∀ x →
  x ≡ Real.ιℚ 0 → Abs.absℝ x ≡ Real.ιℚ 0
eq-zero→abs-eq-zero x x≡0 =
  cong Abs.absℝ x≡0 ∙ Abs.absℝ-zero
