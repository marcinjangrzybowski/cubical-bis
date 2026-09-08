module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.CircleComparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (zero)
open import Cubical.Data.Int using (ℤ; isSetℤ)
import Cubical.Data.Int.Fast as Fast
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.S1 as S¹
import Cubical.Homotopy.Group.Base as Synthetic
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups
open import Cubical.HITs.CauchyReals.Circle.FundamentalGroup as Real
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Algebra using (IntegerAbGroup)

-- Synthetic π₁(S¹) is the set truncation of the HIT's path loop space.
synthetic-circle≅ℤ : GroupIso (Synthetic.πGr zero (S¹.S¹ , S¹.base)) ℤGroup
synthetic-circle≅ℤ =
  compIso (ST.setTruncIdempotentIso S¹.isSetΩS¹) S¹.ΩS¹Isoℤ ,
  makeIsGroupHom (ST.elim2 (λ _ _ → isProp→isSet (isSetℤ _ _)) S¹.winding-hom)

-- The two integer developments have the same carrier and provably equal
-- addition operations. No integer representation is silently identified.
private
  fast-integers≅integers : GroupIso (AbGroup→Group IntegerAbGroup) ℤGroup
  fast-integers≅integers = idIso , makeIsGroupHom (λ k l → sym (Fast.+≡+f k l))

-- An unconditional comparison between real loops and synthetic HIT loops.
-- It identifies the two winding-number classifications as group maps.
real-circle≅synthetic-circle :
  GroupIso Real.CircleLoopGroup (Synthetic.πGr zero (S¹.S¹ , S¹.base))
real-circle≅synthetic-circle = compGroupIso Real.circleLoop≅ℤ
  (compGroupIso fast-integers≅integers (invGroupIso synthetic-circle≅ℤ))

circle-comparison-winding : (c : Real.LoopClass) →
  Iso.fun (fst synthetic-circle≅ℤ) (Iso.fun (fst real-circle≅synthetic-circle) c) ≡
  Real.loopClassWinding c
circle-comparison-winding c = Iso.sec (fst synthetic-circle≅ℤ) (Real.loopClassWinding c)
