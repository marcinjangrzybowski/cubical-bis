module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Clamp where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Negation
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Order


-- A closed-interval clamp is definable solely from the native lattice.
-- Its nonexpansiveness uses the arbitrary-real endpoint theorem, rather
-- than routing through a comparison with another real construction.

clampInterval : Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
clampInterval a b x = (a ⊔ℝ x) ⊓ℝ b


clampInterval-pres≈ : ∀ a b x y ε →
  x Real.Base.≈ᶜ[ ε ] y →
  clampInterval a b x Real.Base.≈ᶜ[ ε ] clampInterval a b y
clampInterval-pres≈ a b x y ε x≈y =
  min-pres≈₁ (a ⊔ℝ x) (a ⊔ℝ y) b ε
    (max-pres≈₂ a x y ε x≈y)


clampIntervalIsNonExpanding : ∀ a b →
  IsNonExpanding
    (snd Real.ℝPremetricSpace) (clampInterval a b)
    (snd Real.ℝPremetricSpace)
clampIntervalIsNonExpanding a b .IsNonExpanding.pres≈ x y ε =
  clampInterval-pres≈ a b x y ε


clampIntervalLowerBound : ∀ a b →
  a ≤ℝ b → ∀ x → a ≤ℝ clampInterval a b x
clampIntervalLowerBound a b a≤b x =
  min-greatest (a ⊔ℝ x) b a
    (max-upper-left a x) a≤b


clampIntervalUpperBound : ∀ a b x →
  clampInterval a b x ≤ℝ b
clampIntervalUpperBound a b x =
  min-lower-right (a ⊔ℝ x) b


clampIntervalFixpoint : ∀ a b x →
  a ≤ℝ x → x ≤ℝ b →
  clampInterval a b x ≡ x
clampIntervalFixpoint a b x a≤x x≤b =
    cong (_⊓ℝ b) a≤x
  ∙ ≤ℝ→min x b x≤b


clampIntervalIdempotent : ∀ a b →
  a ≤ℝ b → ∀ x →
  clampInterval a b (clampInterval a b x) ≡
    clampInterval a b x
clampIntervalIdempotent a b a≤b x =
  clampIntervalFixpoint a b (clampInterval a b x)
    (clampIntervalLowerBound a b a≤b x)
    (clampIntervalUpperBound a b x)


-- The symmetric interval [-r,r] is propositionally the same subspace as
-- the closed absolute-value ball.  Keeping both directions explicit makes
-- the interval and radius APIs interoperate without untruncating data.

absBound→symmetricIntervalBounds : ∀ radius x →
  Abs.absℝ x ≤ℝ radius →
  ((Neg.- radius) ≤ℝ x) × (x ≤ℝ radius)
absBound→symmetricIntervalBounds radius x absx≤radius =
  lower-bound , upper-bound
  where
  lower-bound : (Neg.- radius) ≤ℝ x
  lower-bound =
    subst ((Neg.- radius) ≤ℝ_)
      (Neg.neg-involutive x)
      (neg-reverses≤ (Neg.- x) radius
        (≤ℝ-trans (Neg.- x) (Abs.absℝ x) radius
          (neg-x≤abs x) absx≤radius))

  upper-bound : x ≤ℝ radius
  upper-bound =
    ≤ℝ-trans x (Abs.absℝ x) radius
      (x≤abs x) absx≤radius


symmetricIntervalBounds→absBound : ∀ radius x →
  (Neg.- radius) ≤ℝ x →
  x ≤ℝ radius →
  Abs.absℝ x ≤ℝ radius
symmetricIntervalBounds→absBound radius x lower upper =
  bounds→abs≤ x radius upper
    (subst ((Neg.- x) ≤ℝ_)
      (Neg.neg-involutive radius)
      (neg-reverses≤ (Neg.- radius) x lower))


symmetricIntervalLower≤Upper : ∀ radius →
  Real.ιℚ 0 ≤ℝ radius →
  (Neg.- radius) ≤ℝ radius
symmetricIntervalLower≤Upper radius 0≤radius =
  ≤ℝ-trans (Neg.- radius) (Real.ιℚ 0) radius
    (subst ((Neg.- radius) ≤ℝ_)
      neg-zero
      (neg-reverses≤ (Real.ιℚ 0) radius 0≤radius))
    0≤radius


clampSymmetricAbsBound : ∀ radius →
  Real.ιℚ 0 ≤ℝ radius → ∀ x →
  Abs.absℝ (clampInterval (Neg.- radius) radius x) ≤ℝ radius
clampSymmetricAbsBound radius 0≤radius x =
  symmetricIntervalBounds→absBound radius
    (clampInterval (Neg.- radius) radius x)
    (clampIntervalLowerBound (Neg.- radius) radius
      (symmetricIntervalLower≤Upper radius 0≤radius) x)
    (clampIntervalUpperBound (Neg.- radius) radius x)


clampSymmetricFixpointFromAbs : ∀ radius x →
  Abs.absℝ x ≤ℝ radius →
  clampInterval (Neg.- radius) radius x ≡ x
clampSymmetricFixpointFromAbs radius x absx≤radius =
  clampIntervalFixpoint (Neg.- radius) radius x
    (fst (absBound→symmetricIntervalBounds radius x absx≤radius))
    (snd (absBound→symmetricIntervalBounds radius x absx≤radius))
