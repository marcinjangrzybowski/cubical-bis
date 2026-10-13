module Cubical.Analysis.Real.Integer where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Int.Fast as ℤ using (ℤ)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Base as ℚ using ([_/_])
import Cubical.Data.Rationals.Properties as ℚ
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using ([_/_]₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup

integer : ℤ → ℝ
integer k = rat [ k / 1 ]

integer-injective : ∀ {k l} → integer k ≡ integer l → k ≡ l
integer-injective {k} {l} p =
  sym (ℤ.·IdR k) ∙ ℚ.eq/⁻¹ (k , 1) (l , 1) (rat-injective p) ∙ ℤ.·IdR l

integer-add : ∀ k l → integer k + integer l ≡ integer (k ℤ.+ l)
integer-add k l = rat+rat [ k / 1 ] [ l / 1 ] ∙ cong rat (ℚ.ℤ+→ℚ+ k l)

integer-neg : ∀ k → - integer k ≡ integer (ℤ.- k)
integer-neg k = neg-rat [ k / 1 ] ∙ cong rat (sym (ℚ.-[/] 1 k))

-- A strict distance of less than one separates integer points.  The proof
-- reflects the native real premetric back to rational arithmetic.
integer-separated : ∀ k l → integer k ∼[ [ 1 / 1 ]₊ ] integer l → k ≡ l
integer-separated k l close =
  ℚ.distFromℤ k l (rat-rat-reflects [ k / 1 ] [ l / 1 ] [ 1 / 1 ]₊ close)
