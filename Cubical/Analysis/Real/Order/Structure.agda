module Cubical.Analysis.Real.Order.Structure where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing.Base using (CommRingStr)
open import Cubical.Algebra.OrderedCommRing.Base
  using
    ( IsOrderedCommRing; OrderedCommRing; OrderedCommRingStr
    ; IsOrderedCommRingHom; OrderedCommRingHom
    ; makeIsOrderedCommRingHom
    )
import Cubical.Algebra.OrderedCommRing.Instances.Rationals as ℚInstance
open import Cubical.Data.Rationals.Base as ℚBase
open import Cubical.Data.NatPlusOne
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ

open import Cubical.Relation.Binary.Order.Pseudolattice.Base
  using (PseudolatticeStr)

open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Algebra.Negation using (-_)
open import Cubical.Analysis.Real.Algebra.Addition using (_+_; rat+rat)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_; mul-rat)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Algebra.CommRing using (ℝCommRing)
open import Cubical.Analysis.Real.Order.Base using (_≤ℝ_)
open import Cubical.Analysis.Real.Order.Addition using (addPres≤R)
open import Cubical.Analysis.Real.Order.Lattice using (ℝ≤Pseudolattice)
open import Cubical.Analysis.Real.Order.Multiplication using (mulPres≤R-0≤)
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Rational
  using (<ℚ→<ℝ; <ℝ→<ℚ)
open import Cubical.Analysis.Real.Order.Strict.Properties
  using (<ℝ-weaken; ≤<ℝ-trans; <≤ℝ-trans)
open import Cubical.Analysis.Real.Order.Strict.Addition using (<ℝ-addR)
open import Cubical.Analysis.Real.Order.Strict.Multiplication
  using (mulPres<PosR)
open import Cubical.Analysis.Real.Order.Strict.Located
  using (≤notGreaterEquiv; positiveSum→positiveSummand)
open import Cubical.Analysis.Real.Order.Strict.Structure
  using (isStrictOrder<ℝ)


isOrderedCommRingℝ :
  IsOrderedCommRing 0ℝ 1ℝ _+_ _·_ -_ _<ℝ_ _≤ℝ_
isOrderedCommRingℝ .IsOrderedCommRing.isCommRing =
  CommRingStr.isCommRing (ℝCommRing .snd)
isOrderedCommRingℝ .IsOrderedCommRing.isPseudolattice =
  PseudolatticeStr.is-pseudolattice (ℝ≤Pseudolattice .snd)
isOrderedCommRingℝ .IsOrderedCommRing.isStrictOrder = isStrictOrder<ℝ
isOrderedCommRingℝ .IsOrderedCommRing.<-≤-weaken = <ℝ-weaken
isOrderedCommRingℝ .IsOrderedCommRing.≤≃¬> = ≤notGreaterEquiv
isOrderedCommRingℝ .IsOrderedCommRing.+MonoR≤ = addPres≤R
isOrderedCommRingℝ .IsOrderedCommRing.+MonoR< = <ℝ-addR
isOrderedCommRingℝ .IsOrderedCommRing.posSum→pos∨pos =
  positiveSum→positiveSummand
isOrderedCommRingℝ .IsOrderedCommRing.<-≤-trans = <≤ℝ-trans
isOrderedCommRingℝ .IsOrderedCommRing.≤-<-trans = ≤<ℝ-trans
isOrderedCommRingℝ .IsOrderedCommRing.·MonoR≤ = mulPres≤R-0≤
isOrderedCommRingℝ .IsOrderedCommRing.·MonoR< = mulPres<PosR
isOrderedCommRingℝ .IsOrderedCommRing.0<1 =
  <ℚ→<ℝ 0 1 (ℚ.0<pos 0 1)

ℝOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
ℝOrderedCommRing .fst = ℝ
ℝOrderedCommRing .snd .OrderedCommRingStr.0r = 0ℝ
ℝOrderedCommRing .snd .OrderedCommRingStr.1r = 1ℝ
ℝOrderedCommRing .snd .OrderedCommRingStr._+_ = _+_
ℝOrderedCommRing .snd .OrderedCommRingStr._·_ = _·_
ℝOrderedCommRing .snd .OrderedCommRingStr.-_ = -_
ℝOrderedCommRing .snd .OrderedCommRingStr._<_ = _<ℝ_
ℝOrderedCommRing .snd .OrderedCommRingStr._≤_ = _≤ℝ_
ℝOrderedCommRing .snd .OrderedCommRingStr.isOrderedCommRing =
  isOrderedCommRingℝ

ratIsOrderedCommRingHom :
  IsOrderedCommRingHom
    (ℚInstance.ℚOrderedCommRing .snd) rat
    (ℝOrderedCommRing .snd)
ratIsOrderedCommRingHom = makeIsOrderedCommRingHom
  refl
  (λ p q → sym (rat+rat p q))
  (λ p q → sym (mul-rat p q))
  <ℝ→<ℚ

ratOrderedCommRingHom :
  OrderedCommRingHom ℚInstance.ℚOrderedCommRing ℝOrderedCommRing
ratOrderedCommRingHom = rat , ratIsOrderedCommRingHom
