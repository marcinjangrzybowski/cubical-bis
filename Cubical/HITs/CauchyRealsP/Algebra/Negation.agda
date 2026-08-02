module Cubical.HITs.CauchyRealsP.Algebra.Negation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyRealsP.Foundation

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Completion.Properties.Lift

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

private
  rationalNegation : NE[ ℚPremetricSpace , ℝPremetricSpace ]
  fst rationalNegation x = rat (ℚ.- x)
  IsNonExpanding.pres≈ (snd rationalNegation) x y ε x≈y =
    rat-rat _ _ ε
      (subst (ℚ._< ⟨ ε ⟩₊)
        (abs-Comm x y
        ∙ cong
            {x = y ℚ.- x}
            {y = (ℚ.- x) ℚ.- (ℚ.- y)}
            abs ℚ!)
        x≈y)

  module NegationExtension =
    LiftCompleteCodomain ℚPremetricSpace ℝPremetricSpace isCompleteℝ

  negationExtension =
    NegationExtension.liftNonExpandingExtension rationalNegation

infix 8 -_

-_ : ℝ → ℝ
-_ = fst (fst negationExtension)

neg-rat : ∀ q → - rat q ≡ rat (ℚ.- q)
neg-rat = funExt⁻ (snd negationExtension)

negIsNonExpanding :
  IsNonExpanding (snd ℝPremetricSpace) -_ (snd ℝPremetricSpace)
negIsNonExpanding = snd (fst negationExtension)

negPres∼ : ∀ x y ε
  → x ∼[ ε ] y
  → (- x) ∼[ ε ] (- y)
negPres∼ x y ε =
  IsNonExpanding.pres≈ negIsNonExpanding x y ε
