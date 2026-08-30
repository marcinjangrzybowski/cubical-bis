module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.OrderedCommRing where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Located
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Multiplication
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing


ℝ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℝ≤Pseudolattice =
  makePseudolatticeFromPoset
    ℝFormulaPoset _⊓ℝ_ _⊔ℝ_
    (λ {a b} → min-lower-left a b)
    (λ {a b} → min-lower-right a b)
    (λ {a b x} → min-greatest a b x)
    (λ {a b} → max-upper-left a b)
    (λ {a b} → max-upper-right a b)
    (λ {a b x} → max-least a b x)


isStrictOrderℝ : IsStrictOrder _<ℝ_
isStrictOrderℝ .IsStrictOrder.is-set = Real.Base.isSetCompletion
isStrictOrderℝ .IsStrictOrder.is-prop-valued = isProp<ℝ
isStrictOrderℝ .IsStrictOrder.is-irrefl = <ℝ-irrefl
isStrictOrderℝ .IsStrictOrder.is-trans = <ℝ-trans
isStrictOrderℝ .IsStrictOrder.is-asym = <ℝ-asym
isStrictOrderℝ .IsStrictOrder.is-weakly-linear = isWeaklyLinear<ℝ


ℝ≪StrictOrder : StrictOrder ℓ-zero ℓ-zero
ℝ≪StrictOrder = strictorder Real.ℝ _<ℝ_ isStrictOrderℝ


isOrderedCommRingℝ :
  IsOrderedCommRing
    (Real.ιℚ 0) (Real.ιℚ 1)
    Add._+_ Mul._·_ Neg.-_
    _<ℝ_ _≤ℝ_
isOrderedCommRingℝ .IsOrderedCommRing.isCommRing =
  CommRingStr.isCommRing (snd ℝCommRing)
isOrderedCommRingℝ .IsOrderedCommRing.isPseudolattice =
  PseudolatticeStr.is-pseudolattice (snd ℝ≤Pseudolattice)
isOrderedCommRingℝ .IsOrderedCommRing.isStrictOrder =
  isStrictOrderℝ
isOrderedCommRingℝ .IsOrderedCommRing.<-≤-weaken =
  <ℝ-weaken
isOrderedCommRingℝ .IsOrderedCommRing.≤≃¬> =
  ≤NotPositiveGreaterEquiv
isOrderedCommRingℝ .IsOrderedCommRing.+MonoR≤ =
  add-preserves≤-right
isOrderedCommRingℝ .IsOrderedCommRing.+MonoR< =
  <ℝ-add-right
isOrderedCommRingℝ .IsOrderedCommRing.posSum→pos∨pos =
  positiveSum→positiveSummand
isOrderedCommRingℝ .IsOrderedCommRing.<-≤-trans =
  ≪≤ℝ-trans
isOrderedCommRingℝ .IsOrderedCommRing.≤-<-trans =
  ≤<ℝ-trans
isOrderedCommRingℝ .IsOrderedCommRing.·MonoR≤ =
  λ x y z 0≤z x≤y →
    mul-preserves≤-right-nonnegative x y z x≤y 0≤z
isOrderedCommRingℝ .IsOrderedCommRing.·MonoR< =
  λ x y z 0≪z x≪y →
    mul-preserves≪-right-positive x y z x≪y 0≪z
isOrderedCommRingℝ .IsOrderedCommRing.0<1 =
  <ℚ→<ℝ 0 1 (OrderedCommRingStr.0<1 (snd ℚOrderedCommRing))


ℝOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
fst ℝOrderedCommRing = Real.ℝ
OrderedCommRingStr.0r (snd ℝOrderedCommRing) = Real.ιℚ 0
OrderedCommRingStr.1r (snd ℝOrderedCommRing) = Real.ιℚ 1
OrderedCommRingStr._+_ (snd ℝOrderedCommRing) = Add._+_
OrderedCommRingStr._·_ (snd ℝOrderedCommRing) = Mul._·_
OrderedCommRingStr.-_ (snd ℝOrderedCommRing) = Neg.-_
OrderedCommRingStr._<_ (snd ℝOrderedCommRing) = _<ℝ_
OrderedCommRingStr._≤_ (snd ℝOrderedCommRing) = _≤ℝ_
OrderedCommRingStr.isOrderedCommRing (snd ℝOrderedCommRing) =
  isOrderedCommRingℝ


ιℚIsOrderedCommRingHom :
  IsOrderedCommRingHom
    (snd ℚOrderedCommRing) Real.ιℚ
    (snd ℝOrderedCommRing)
ιℚIsOrderedCommRingHom =
  makeIsOrderedCommRingHom
    refl
    (λ p q → sym (Add.add-ι-ι p q))
    (λ p q → sym (Mul.mul-ι-ι p q))
    (<ℝ→<ℚ)


ιℚOrderedCommRingHom :
  OrderedCommRingHom ℚOrderedCommRing ℝOrderedCommRing
ιℚOrderedCommRingHom = Real.ιℚ , ιℚIsOrderedCommRingHom
