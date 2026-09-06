module Cubical.HITs.CauchyReals.Circle.Homotopy.Classification where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Int.Fast as ℤ using (ℤ)
open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.HITs.CauchyReals.Circle.UniformGroup
open import Cubical.HITs.CauchyReals.Circle.Winding
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Base
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Algebra
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Quotient
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Integers
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Lifted
open import Cubical.HITs.CauchyReals.Circle.Core using (injCircle)
open import Cubical.HITs.CauchyReals.Foundation.Base using (ℝ)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base using (ℝ₊; absᵣ; _≤ᵣ_)
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric using (ℝPremetricSpace)
open import Cubical.Relation.Premetric.Mappings using (UC[_,_])

-- An abstract criterion for classification. NullHomotopy constructs its
-- proof; Equivalence applies the criterion to obtain the group isomorphism.
NullWindingIsNull : Type
NullWindingIsNull = (f : CircleMap) → windingNumber f ≡ 0 → Homotopic f zeroCircleMap

private
  module C = AbGroupStr (snd CircleHomotopyAbGroup)
  module CG = GroupTheory (AbGroup→Group CircleHomotopyAbGroup)

nullWinding→injective : NullWindingIsNull →
  (x y : CircleHomotopyClasses) → classWinding x ≡ classWinding y → x ≡ y
nullWinding→injective null = SQ.elimProp2 (λ _ _ → isProp→ (SQ.squash/ _ _)) compare
  where
  compare : (f g : CircleMap) → windingNumber f ≡ windingNumber g → class f ≡ class g
  compare f g same = CG.·CancelR (negClass (class g))
    (SQ.eq/ _ _ (null difference degree-zero) ∙ sym (C.+InvR (class g)))
    where
    difference : CircleMap
    difference = addCircleUC f (negCircleUC g)
    degree-zero : windingNumber difference ≡ 0
    degree-zero = windingNumber-add f (negCircleUC g)
      ∙ cong (ℤ._+_ (windingNumber f)) (IsGroupHom.presinv (snd windingHom) g)
      ∙ cong (ℤ._+ (ℤ.- windingNumber g)) same
      ∙ ℤ.-Cancel (windingNumber g)

injective→nullWinding :
  ((x y : CircleHomotopyClasses) → classWinding x ≡ classWinding y → x ≡ y) →
  NullWindingIsNull
injective→nullWinding injective f degree-zero = class-effective f zeroCircleMap
  (injective (class f) (class zeroCircleMap)
    (degree-zero ∙ sym (IsGroupHom.pres1 (snd windingHom))))

-- The algebraic passage from null-homotopies to a group isomorphism.
classificationFromNullWinding : NullWindingIsNull →
  AbGroupIso CircleHomotopyAbGroup IntegerAbGroup
classificationFromNullWinding null = equivalence , snd classWindingHom
  where
  equivalence : Iso CircleHomotopyClasses ℤ
  Iso.fun equivalence = classWinding
  Iso.inv equivalence = integerClass
  Iso.sec equivalence = winding-integerClass
  Iso.ret equivalence x = nullWinding→injective null (integerClass (classWinding x)) x
    (winding-integerClass (classWinding x))

-- A more concrete sufficient obligation. Existence is truncated, and
-- the proof below does not select logarithms simultaneously for maps.
BoundedCircleLog : CircleMap → Type
BoundedCircleLog f = Σ[ g ∈ UC[ CirclePremetricSpace , ℝPremetricSpace ] ]
  Σ[ B ∈ ℝ₊ ] (∀ x → absᵣ (fst g x) ≤ᵣ fst B) ×
    (∀ x → injCircle (fst g x) ≡ fst f x)

ZeroWindingHasLog : Type
ZeroWindingHasLog = (f : CircleMap) → windingNumber f ≡ 0 → ∥ BoundedCircleLog f ∥₁

logLift→nullWinding : ZeroWindingHasLog → NullWindingIsNull
logLift→nullWinding existsLog f degree-zero = PT.rec squash₁
  (λ (g , B , bound , lifts) → lifted-null f g B bound lifts) (existsLog f degree-zero)

classificationFromLogLift : ZeroWindingHasLog →
  AbGroupIso CircleHomotopyAbGroup IntegerAbGroup
classificationFromLogLift existsLog = classificationFromNullWinding (logLift→nullWinding existsLog)
