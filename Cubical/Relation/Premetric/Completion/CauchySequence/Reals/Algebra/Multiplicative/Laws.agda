module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
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
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul

import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CauchyGraph.Binary
  as BinaryDefinition

private
  module B = BinaryDefinition
    ℚPremetricSpace ℚPremetricSpace ℚPremetricSpace

  multiplicationGraph : ℚ → ℚ → Real.ℝ
  multiplicationGraph p q = Real.ιℚ (Mul.rationalMultiplication p q)


opaque
  commuted-multiplication-joint : ∀ x y →
    B.BaseGraphClosure
      Mul.rationalMultiplication x y (y Mul.· x)
  commuted-multiplication-joint x y α β γ =
    PT.map swap (Mul.multiplication-joint y x β α γ)
    where
    swap :
      (Σ[ q ∈ ℚ ]
        Σ[ p ∈ ℚ ]
          (Real.ιℚ q Real.Base.≈ᶜ[ β ] y) ×
          (Real.ιℚ p Real.Base.≈ᶜ[ α ] x) ×
          (Real.ιℚ (Mul.rationalMultiplication q p)
            Real.Base.≈ᶜ[ γ ] (y Mul.· x))) →
      Σ[ p ∈ ℚ ]
        Σ[ q ∈ ℚ ]
          (Real.ιℚ p Real.Base.≈ᶜ[ α ] x) ×
          (Real.ιℚ q Real.Base.≈ᶜ[ β ] y) ×
          (Real.ιℚ (Mul.rationalMultiplication p q)
            Real.Base.≈ᶜ[ γ ] (y Mul.· x))
    swap (q , p , q∼y , p∼x , product∼) =
      p , q , p∼x , q∼y ,
      subst
        (λ r → Real.ιℚ r Real.Base.≈ᶜ[ γ ] (y Mul.· x))
        (ℚ.·Comm q p) product∼


mul-comm : ∀ x y → x Mul.· y ≡ y Mul.· x
mul-comm x y =
  B.graphClosureUnique multiplicationGraph
    Mul.rationalMultiplication-preservesCauchyGraphs x y
    (x Mul.· y) (y Mul.· x)
    (Mul.multiplication-joint x y)
    (commuted-multiplication-joint x y)


opaque
  multiplication-right-zero-joint : ∀ x →
    B.BaseGraphClosure Mul.rationalMultiplication
      x (Real.ιℚ 0) (Real.ιℚ 0)
  multiplication-right-zero-joint x α β γ =
    PT.map approximate (Real.rationalsDense x α)
    where
    approximate :
      (Σ[ p ∈ ℚ ] (Real.ιℚ p Real.Base.≈ᶜ[ α ] x)) →
      Σ[ p ∈ ℚ ]
        Σ[ q ∈ ℚ ]
          (Real.ιℚ p Real.Base.≈ᶜ[ α ] x) ×
          (Real.ιℚ q Real.Base.≈ᶜ[ β ] Real.ιℚ 0) ×
          (Real.ιℚ (Mul.rationalMultiplication p q)
            Real.Base.≈ᶜ[ γ ] Real.ιℚ 0)
    approximate (p , p∼x) =
      p , 0 , p∼x
      , Real.Base.isRefl≈ᶜ (Real.ιℚ 0) β
      , subst
          (λ r → Real.ιℚ r Real.Base.≈ᶜ[ γ ] Real.ιℚ 0)
          (sym ℚ!)
          (Real.Base.isRefl≈ᶜ (Real.ιℚ 0) γ)


mul-zero-right : ∀ x → x Mul.· Real.ιℚ 0 ≡ Real.ιℚ 0
mul-zero-right x =
  B.graphClosureUnique multiplicationGraph
    Mul.rationalMultiplication-preservesCauchyGraphs x (Real.ιℚ 0)
    (x Mul.· Real.ιℚ 0) (Real.ιℚ 0)
    (Mul.multiplication-joint x (Real.ιℚ 0))
    (multiplication-right-zero-joint x)


mul-zero-left : ∀ x → Real.ιℚ 0 Mul.· x ≡ Real.ιℚ 0
mul-zero-left x =
  mul-comm (Real.ιℚ 0) x ∙ mul-zero-right x


opaque
  multiplication-right-one-joint : ∀ x →
    B.BaseGraphClosure Mul.rationalMultiplication
      x (Real.ιℚ 1) x
  multiplication-right-one-joint x α β γ =
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
          (Real.ιℚ q Real.Base.≈ᶜ[ β ] Real.ιℚ 1) ×
          (Real.ιℚ (Mul.rationalMultiplication p q)
            Real.Base.≈ᶜ[ γ ] x)
    approximate (p , p∼x) =
      p , 1
      , Real.Base.isMonotone≈ᶜ< _ _ κ α
          (min/2₊<L α γ) p∼x
      , Real.Base.isRefl≈ᶜ (Real.ιℚ 1) β
      , subst
          (λ r → Real.ιℚ r Real.Base.≈ᶜ[ γ ] x)
          (sym ℚ!)
          (Real.Base.isMonotone≈ᶜ< _ _ κ γ
            (min/2₊<R α γ) p∼x)


mul-one-right : ∀ x → x Mul.· Real.ιℚ 1 ≡ x
mul-one-right x =
  B.graphClosureUnique multiplicationGraph
    Mul.rationalMultiplication-preservesCauchyGraphs x (Real.ιℚ 1)
    (x Mul.· Real.ιℚ 1) x
    (Mul.multiplication-joint x (Real.ιℚ 1))
    (multiplication-right-one-joint x)


mul-one-left : ∀ x → Real.ιℚ 1 Mul.· x ≡ x
mul-one-left x =
  mul-comm (Real.ιℚ 1) x ∙ mul-one-right x
