module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.Relation.Premetric.Instances.Rationals using
  (ℚPremetricSpace)

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg

import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CauchyGraph.Binary
  as BinaryDefinition

private
  module B = BinaryDefinition
    ℚPremetricSpace ℚPremetricSpace ℚPremetricSpace

  additionGraph : ℚ → ℚ → Real.ℝ
  additionGraph = λ p q → Real.Base.ι (Add.rationalAddition p q)


opaque
 commuted-addition-joint : ∀ x y →
   B.BaseGraphClosure
     Add.rationalAddition x y (y Add.+ x)
 commuted-addition-joint x y α β γ =
   PT.map swap (Add.addition-joint y x β α γ)
   where
   swap :
     (Σ[ q ∈ ℚ ]
       Σ[ p ∈ ℚ ]
         (Real.ιℚ q Real.Base.≈ᶜ[ β ] y) ×
         (Real.ιℚ p Real.Base.≈ᶜ[ α ] x) ×
         (Real.ιℚ (Add.rationalAddition q p)
           Real.Base.≈ᶜ[ γ ] (y Add.+ x))) →
     Σ[ p ∈ ℚ ]
       Σ[ q ∈ ℚ ]
         (Real.ιℚ p Real.Base.≈ᶜ[ α ] x) ×
         (Real.ιℚ q Real.Base.≈ᶜ[ β ] y) ×
         (Real.ιℚ (Add.rationalAddition p q)
           Real.Base.≈ᶜ[ γ ] (y Add.+ x))
   swap (q , p , q∼y , p∼x , sum∼) =
     p , q , p∼x , q∼y ,
     subst
       (λ r → Real.ιℚ r Real.Base.≈ᶜ[ γ ] (y Add.+ x))
       (ℚR.+Comm q p) sum∼


add-comm : ∀ x y → x Add.+ y ≡ y Add.+ x
add-comm x y =
  B.graphClosureUnique additionGraph
    Add.rationalAddition-preservesCauchyGraphs x y
    (x Add.+ y) (y Add.+ x)
    (Add.addition-joint x y)
    (commuted-addition-joint x y)


opaque
 right-zero-joint : ∀ x →
   B.BaseGraphClosure Add.rationalAddition
     x (Real.ιℚ 0) x
 right-zero-joint x α β γ =
   PT.map approximate
     (Real.rationalsDense x (min₊ α γ /2₊))
   where
   κ : ℚ₊
   κ = min₊ α γ /2₊

   approximate :
     (Σ[ p ∈ ℚ ] (Real.ιℚ p Real.Base.≈ᶜ[ κ ] x)) →
     Σ[ p ∈ ℚ ]
       Σ[ q ∈ ℚ ]
         (Real.ιℚ p Real.Base.≈ᶜ[ α ] x) ×
         (Real.ιℚ q Real.Base.≈ᶜ[ β ] Real.ιℚ 0) ×
         (Real.ιℚ (Add.rationalAddition p q)
           Real.Base.≈ᶜ[ γ ] x)
   approximate (p , p∼x) =
     p , 0
     , Real.Base.isMonotone≈ᶜ< _ _ κ α
         (min/2₊<L α γ) p∼x
     , Real.Base.isRefl≈ᶜ (Real.ιℚ 0) β
     , subst
         (λ r → Real.ιℚ r Real.Base.≈ᶜ[ γ ] x)
         (sym ℚ!)
         (Real.Base.isMonotone≈ᶜ< _ _ κ γ
           (min/2₊<R α γ) p∼x)


add-zero-right : ∀ x → x Add.+ Real.ιℚ 0 ≡ x
add-zero-right x =
  B.graphClosureUnique additionGraph
    Add.rationalAddition-preservesCauchyGraphs x (Real.ιℚ 0)
    (x Add.+ Real.ιℚ 0) x
    (Add.addition-joint x (Real.ιℚ 0))
    (right-zero-joint x)

add-zero-left : ∀ x → Real.ιℚ 0 Add.+ x ≡ x
add-zero-left x =
  add-comm (Real.ιℚ 0) x ∙ add-zero-right x


opaque
 inverse-addition-joint : ∀ x →
   B.BaseGraphClosure Add.rationalAddition
     x (Neg.- x) (Real.ιℚ 0)
 inverse-addition-joint x α β γ =
   PT.map approximate (Real.rationalsDense x (min₊ α β /2₊))
   where
   κ : ℚ₊
   κ = min₊ α β /2₊

   approximate :
     (Σ[ p ∈ ℚ ] (Real.ιℚ p Real.Base.≈ᶜ[ κ ] x)) →
     Σ[ p ∈ ℚ ]
       Σ[ q ∈ ℚ ]
         (Real.ιℚ p Real.Base.≈ᶜ[ α ] x) ×
         (Real.ιℚ q Real.Base.≈ᶜ[ β ] (Neg.- x)) ×
         (Real.ιℚ (Add.rationalAddition p q)
           Real.Base.≈ᶜ[ γ ] Real.ιℚ 0)
   approximate (p , p∼x) =
     p , (ℚR.- p)
     , Real.Base.isMonotone≈ᶜ< _ _ κ α
         (min/2₊<L α β) p∼x
     , Real.Base.isMonotone≈ᶜ< _ _ κ β
         (min/2₊<R α β)
         (subst
           (Real.Base._≈ᶜ[ κ ] (Neg.- x))
           (Neg.neg-ι p)
           (Neg.neg-pres≈ (Real.ιℚ p) x κ p∼x))
     , subst
         (λ r → Real.ιℚ r Real.Base.≈ᶜ[ γ ] Real.ιℚ 0)
         (sym ℚ!)
         (Real.Base.isRefl≈ᶜ (Real.ιℚ 0) γ)


add-inverse-right : ∀ x → x Add.+ (Neg.- x) ≡ Real.ιℚ 0
add-inverse-right x =
  B.graphClosureUnique additionGraph
    Add.rationalAddition-preservesCauchyGraphs x (Neg.- x)
    (x Add.+ (Neg.- x)) (Real.ιℚ 0)
    (Add.addition-joint x (Neg.- x))
    (inverse-addition-joint x)

add-inverse-left : ∀ x → (Neg.- x) Add.+ x ≡ Real.ιℚ 0
add-inverse-left x =
  add-comm (Neg.- x) x ∙ add-inverse-right x
