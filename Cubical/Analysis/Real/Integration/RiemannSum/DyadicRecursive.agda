module Cubical.Analysis.Real.Integration.RiemannSum.DyadicRecursive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open 1/2∈ℚ using (/2+/2≡id)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Scalar
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Series.Geometric.Rational
  using (halfℚ; halfℚPath)
open import Cubical.Analysis.Real.Integration.Partition.Mesh


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  split-widths : ∀ a m b →
    (m - a) + (b - m) ≡ b - a
  split-widths a m b =
    ℝRing.+ShufflePairs m (- a) b (- m)
    ∙ cong₂ _+_
        (addComm m b) (addComm (- a) (- m))
    ∙ sym (addAssoc b m ((- m) + (- a)))
    ∙ cong (b +_) (addAssoc m (- m) (- a))
    ∙ cong (b +_)
        (cong (_+ (- a)) (addInvR m)
        ∙ addIdL (- a))

  sum-difference-split : ∀ x y u v →
    (x + y) - (u + v) ≡
    (x - u) + (y - v)
  sum-difference-split x y u v =
    cong ((x + y) +_) (sym (ℝRing.-Dist u v))
    ∙ ℝRing.+ShufflePairs x y (- u) (- v)

  halfℚ-nonnegative : 0 ℚ.≤ halfℚ
  halfℚ-nonnegative =
    ℚ.<Weaken≤ 0 halfℚ
      (subst (0 ℚ.<_) (sym halfℚPath) (ℚ.pos<pos tt))

  halfℝ-nonnegative : 0ℝ ≤ℝ rat halfℚ
  halfℝ-nonnegative =
    invEq (rat≤rat≃ 0 halfℚ) halfℚ-nonnegative

  half-scalar-pres≤ : ∀ x y → x ≤ℝ y →
    halfℚ ⋆ x ≤ℝ halfℚ ⋆ y
  half-scalar-pres≤ x y x≤y =
    subst2 _≤ℝ_
      (sym (scalar-as-mul halfℚ x))
      (sym (scalar-as-mul halfℚ y))
      (mulPres≤L x y (rat halfℚ)
        (0≤→isNonnegative (rat halfℚ) halfℝ-nonnegative)
        x≤y)

  scalar-sub : ∀ c x y →
    c ⋆ (x - y) ≡ (c ⋆ x) - (c ⋆ y)
  scalar-sub c x y =
    scalar-as-mul c (x - y)
    ∙ ℝRing.·DistR- (rat c) x y
    ∙ cong₂ _-_
        (sym (scalar-as-mul c x))
        (sym (scalar-as-mul c y))


-- Binary subdivision is kept separate from the flat `Fin (2 ^ n)`
-- presentation.  Refinement proofs can therefore recurse on the two halves
-- without quotient/remainder arithmetic on finite indices.

midpoint : ℝ → ℝ → ℝ
midpoint x y = halfℚ ⋆ (x + y)


private
  half-double : ∀ x → midpoint x x ≡ x
  half-double x =
    scalar-dist-right halfℚ x x
    ∙ sym (scalar-dist-left halfℚ halfℚ x)
    ∙ cong (_⋆ x) (/2+/2≡id 1)
    ∙ scalar-id x


midpoint-lower : ∀ x y → x ≤ℝ y → x ≤ℝ midpoint x y
midpoint-lower x y x≤y =
  subst (λ z → z ≤ℝ midpoint x y) (half-double x)
    (half-scalar-pres≤ (x + x) (x + y)
      (addPres≤L x y x x≤y))


midpoint-upper : ∀ x y → x ≤ℝ y → midpoint x y ≤ℝ y
midpoint-upper x y x≤y =
  subst (midpoint x y ≤ℝ_) (half-double y)
    (half-scalar-pres≤ (x + y) (y + y)
      (addPres≤R x y y x≤y))


midpoint-widths : ∀ a b →
  (midpoint a b - a) + (b - midpoint a b) ≡ b - a
midpoint-widths a b =
  split-widths a (midpoint a b) b


midpoint-left-width : ∀ a b →
  midpoint a b - a ≡ halfℚ ⋆ (b - a)
midpoint-left-width a b =
  cong (λ x → midpoint a b - x) (sym (half-double a))
  ∙ sym (scalar-sub halfℚ (a + b) (a + a))
  ∙ cong (halfℚ ⋆_)
      (sum-difference-split a b a a
      ∙ cong₂ _+_ (subSelf a) (refl {x = b - a})
      ∙ addIdL (b - a))


midpoint-right-width : ∀ a b →
  b - midpoint a b ≡ halfℚ ⋆ (b - a)
midpoint-right-width a b =
  cong (λ x → x - midpoint a b) (sym (half-double b))
  ∙ sym (scalar-sub halfℚ (b + b) (a + b))
  ∙ cong (halfℚ ⋆_)
      (sum-difference-split b b a b
      ∙ cong₂ _+_ (refl {x = b - a}) (subSelf b)
      ∙ addIdR (b - a))


dyadicRecursiveSum :
  (ℝ → ℝ) → ℝ → ℝ → ℕ → ℝ
dyadicRecursiveSum f a b zero =
  (b - a) · f a
dyadicRecursiveSum f a b (suc n) =
  dyadicRecursiveSum f a (midpoint a b) n +
  dyadicRecursiveSum f (midpoint a b) b n


dyadicRecursiveSum-constant : ∀ a b c n →
  dyadicRecursiveSum (λ _ → c) a b n ≡
  (b - a) · c
dyadicRecursiveSum-constant a b c zero = refl
dyadicRecursiveSum-constant a b c (suc n) =
  cong₂ _+_
    (dyadicRecursiveSum-constant a (midpoint a b) c n)
    (dyadicRecursiveSum-constant (midpoint a b) b c n)
  ∙ sym (mulDistL
      (midpoint a b - a)
      (b - midpoint a b) c)
  ∙ cong (_· c) (midpoint-widths a b)


dyadicRecursiveSum-add : ∀ f g a b n →
  dyadicRecursiveSum (λ x → f x + g x) a b n ≡
  dyadicRecursiveSum f a b n +
  dyadicRecursiveSum g a b n
dyadicRecursiveSum-add f g a b zero =
  mulDistR (b - a) (f a) (g a)
dyadicRecursiveSum-add f g a b (suc n) =
  cong₂ _+_
    (dyadicRecursiveSum-add f g a (midpoint a b) n)
    (dyadicRecursiveSum-add f g (midpoint a b) b n)
  ∙ ℝRing.+ShufflePairs
      (dyadicRecursiveSum f a (midpoint a b) n)
      (dyadicRecursiveSum g a (midpoint a b) n)
      (dyadicRecursiveSum f (midpoint a b) b n)
      (dyadicRecursiveSum g (midpoint a b) b n)


dyadicRecursiveSum-neg : ∀ f a b n →
  dyadicRecursiveSum (λ x → - f x) a b n ≡
  - dyadicRecursiveSum f a b n
dyadicRecursiveSum-neg f a b zero =
  ℝRing.-DistR· (b - a) (f a)
dyadicRecursiveSum-neg f a b (suc n) =
  cong₂ _+_
    (dyadicRecursiveSum-neg f a (midpoint a b) n)
    (dyadicRecursiveSum-neg f (midpoint a b) b n)
  ∙ sym (negAdd
      (dyadicRecursiveSum f a (midpoint a b) n)
      (dyadicRecursiveSum f (midpoint a b) b n))


dyadicRecursiveSum-scale : ∀ c f a b n →
  dyadicRecursiveSum (λ x → c · f x) a b n ≡
  c · dyadicRecursiveSum f a b n
dyadicRecursiveSum-scale c f a b zero =
  mulAssoc (b - a) c (f a)
  ∙ cong (_· f a) (mulComm (b - a) c)
  ∙ sym (mulAssoc c (b - a) (f a))
dyadicRecursiveSum-scale c f a b (suc n) =
  cong₂ _+_
    (dyadicRecursiveSum-scale c f a (midpoint a b) n)
    (dyadicRecursiveSum-scale c f (midpoint a b) b n)
  ∙ sym (mulDistR c
      (dyadicRecursiveSum f a (midpoint a b) n)
      (dyadicRecursiveSum f (midpoint a b) b n))


-- Uniform closeness to one reference value controls the recursive sum by
-- total width, independently of the subdivision depth.

dyadicRecursiveSum-constantAbsBound :
  ∀ f a b c error n →
  (a≤b : a ≤ℝ b) →
  (∀ x → a ≤ℝ x → x ≤ℝ b →
    absℝ (f x - c) ≤ℝ error) →
  absℝ
    (dyadicRecursiveSum f a b n -
      (b - a) · c)
  ≤ℝ (b - a) · error
dyadicRecursiveSum-constantAbsBound
  f a b c error zero a≤b close =
  subst
    (_≤ℝ (b - a) · error)
    (sym
      (cong absℝ
        (sym (ℝRing.·DistR- (b - a) (f a) c))
      ∙ absMul (b - a) (f a - c)
      ∙ cong (_· absℝ (f a - c))
          (absOfNonnegative
            (b - a) (nonnegativeSub a b a≤b))))
    (mulPres≤L
      (absℝ (f a - c)) error (b - a)
      (0≤→isNonnegative (b - a) (nonnegativeSub a b a≤b))
      (close a (≤ℝ-refl a) a≤b))
dyadicRecursiveSum-constantAbsBound
  f a b c error (suc n) a≤b close =
  subst
    (λ z →
      absℝ
        (dyadicRecursiveSum f a b (suc n) -
          (b - a) · c)
      ≤ℝ z)
    total-bound
    (subst
      (λ z → absℝ z ≤ℝ left-bound + right-bound)
      (sym difference-split)
      combined-bound)
  where
  left-difference : ℝ
  left-difference =
    dyadicRecursiveSum f a (midpoint a b) n -
    (midpoint a b - a) · c

  right-difference : ℝ
  right-difference =
    dyadicRecursiveSum f (midpoint a b) b n -
    (b - midpoint a b) · c

  left-bound : ℝ
  left-bound = (midpoint a b - a) · error

  right-bound : ℝ
  right-bound = (b - midpoint a b) · error

  left-estimate : absℝ left-difference ≤ℝ left-bound
  left-estimate =
    dyadicRecursiveSum-constantAbsBound
      f a (midpoint a b) c error n
      (midpoint-lower a b a≤b)
      (λ x a≤x x≤mid →
        close x a≤x
          (≤ℝ-trans x (midpoint a b) b x≤mid
            (midpoint-upper a b a≤b)))

  right-estimate : absℝ right-difference ≤ℝ right-bound
  right-estimate =
    dyadicRecursiveSum-constantAbsBound
      f (midpoint a b) b c error n
      (midpoint-upper a b a≤b)
      (λ x mid≤x x≤b →
        close x
          (≤ℝ-trans a (midpoint a b) x
            (midpoint-lower a b a≤b) mid≤x)
          x≤b)

  combined-bound :
    absℝ (left-difference + right-difference) ≤ℝ
    left-bound + right-bound
  combined-bound =
    ≤ℝ-trans
      (absℝ (left-difference + right-difference))
      (absℝ left-difference + absℝ right-difference)
      (left-bound + right-bound)
      (absTriangle left-difference right-difference)
      (addPres≤
        (absℝ left-difference) left-bound
        (absℝ right-difference) right-bound
        left-estimate right-estimate)

  difference-split :
    (dyadicRecursiveSum f a (midpoint a b) n +
      dyadicRecursiveSum f (midpoint a b) b n) -
      (b - a) · c
    ≡ left-difference + right-difference
  difference-split =
    cong
      (λ x →
        (dyadicRecursiveSum f a (midpoint a b) n +
          dyadicRecursiveSum f (midpoint a b) b n) - x)
      (cong (_· c) (sym (midpoint-widths a b))
      ∙ mulDistL
          (midpoint a b - a)
          (b - midpoint a b) c)
    ∙ cong
        ((dyadicRecursiveSum f a (midpoint a b) n +
          dyadicRecursiveSum f (midpoint a b) b n) +_)
        (sym (ℝRing.-Dist
          ((midpoint a b - a) · c)
          ((b - midpoint a b) · c)))
    ∙ ℝRing.+ShufflePairs
        (dyadicRecursiveSum f a (midpoint a b) n)
        (dyadicRecursiveSum f (midpoint a b) b n)
        (- ((midpoint a b - a) · c))
        (- ((b - midpoint a b) · c))

  total-bound :
    left-bound + right-bound ≡ (b - a) · error
  total-bound =
    sym (mulDistL
      (midpoint a b - a)
      (b - midpoint a b) error)
    ∙ cong (_· error) (midpoint-widths a b)


-- Oscillation is recorded structurally at the cells of a fixed depth.

DyadicLeftOscillation :
  (ℝ → ℝ) → ℝ → ℝ → ℝ → ℕ → Type₀
DyadicLeftOscillation f error a b zero =
  ∀ x → a ≤ℝ x → x ≤ℝ b →
    absℝ (f x - f a) ≤ℝ error
DyadicLeftOscillation f error a b (suc n) =
  DyadicLeftOscillation f error a (midpoint a b) n ×
  DyadicLeftOscillation f error (midpoint a b) b n


-- Level `n + k` is compared directly with level `n`.  The estimate is
-- uniform in the additional refinement depth `k`, unlike an adjacent-level
-- bound.

dyadicRecursiveSum-refinementAbsBound :
  ∀ f a b error n k →
  (a≤b : a ≤ℝ b) →
  DyadicLeftOscillation f error a b n →
  absℝ
    (dyadicRecursiveSum f a b (n ℕ.+ k) -
      dyadicRecursiveSum f a b n)
  ≤ℝ (b - a) · error
dyadicRecursiveSum-refinementAbsBound
  f a b error zero k a≤b oscillation =
  dyadicRecursiveSum-constantAbsBound
    f a b (f a) error k a≤b oscillation
dyadicRecursiveSum-refinementAbsBound
  f a b error (suc n) k a≤b oscillation =
  subst
    (λ z →
      absℝ
        (dyadicRecursiveSum f a b (suc n ℕ.+ k) -
          dyadicRecursiveSum f a b (suc n))
      ≤ℝ z)
    total-bound
    (subst
      (λ z → absℝ z ≤ℝ left-bound + right-bound)
      (sym difference-split)
      combined-bound)
  where
  left-fine : ℝ
  left-fine = dyadicRecursiveSum f a (midpoint a b) (n ℕ.+ k)

  right-fine : ℝ
  right-fine = dyadicRecursiveSum f (midpoint a b) b (n ℕ.+ k)

  left-coarse : ℝ
  left-coarse = dyadicRecursiveSum f a (midpoint a b) n

  right-coarse : ℝ
  right-coarse = dyadicRecursiveSum f (midpoint a b) b n

  left-difference : ℝ
  left-difference = left-fine - left-coarse

  right-difference : ℝ
  right-difference = right-fine - right-coarse

  left-bound : ℝ
  left-bound = (midpoint a b - a) · error

  right-bound : ℝ
  right-bound = (b - midpoint a b) · error

  left-estimate : absℝ left-difference ≤ℝ left-bound
  left-estimate =
    dyadicRecursiveSum-refinementAbsBound
      f a (midpoint a b) error n k
      (midpoint-lower a b a≤b) (fst oscillation)

  right-estimate : absℝ right-difference ≤ℝ right-bound
  right-estimate =
    dyadicRecursiveSum-refinementAbsBound
      f (midpoint a b) b error n k
      (midpoint-upper a b a≤b) (snd oscillation)

  combined-bound :
    absℝ (left-difference + right-difference) ≤ℝ
    left-bound + right-bound
  combined-bound =
    ≤ℝ-trans
      (absℝ (left-difference + right-difference))
      (absℝ left-difference + absℝ right-difference)
      (left-bound + right-bound)
      (absTriangle left-difference right-difference)
      (addPres≤
        (absℝ left-difference) left-bound
        (absℝ right-difference) right-bound
        left-estimate right-estimate)

  difference-split :
    (left-fine + right-fine) -
      (left-coarse + right-coarse)
    ≡ left-difference + right-difference
  difference-split =
    sum-difference-split
      left-fine right-fine left-coarse right-coarse

  total-bound :
    left-bound + right-bound ≡ (b - a) · error
  total-bound =
    sym (mulDistL
      (midpoint a b - a)
      (b - midpoint a b) error)
    ∙ cong (_· error) (midpoint-widths a b)
