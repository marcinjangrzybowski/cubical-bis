module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as Nat using (ℕ ; max)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Inverse

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Continuity
  using (add-pres≈)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Continuity
  using (mulIsLipschitzLeftAtBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
  using (RationalBound ; ∃rationalBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform


-- Eventual equality of all partial sums, with one cutoff common to the
-- parameter family, preserves uniform Cauchyness.  The cutoff is itself
-- merely given: using it at one requested radius requires no global choice.

UniformlyEventuallyEqualPartialSums : ∀ {ℓ} (X : Type ℓ) →
  (X → RealSequence) → (X → RealSequence) → Type ℓ
UniformlyEventuallyEqualPartialSums X a b =
  ∃[ K ∈ ℕ ]
    (∀ x n → K ℕ.≤ n →
      partialSum (a x) n ≡ partialSum (b x) n)


uniformlyEventuallyEqualPartialSumsPresUniformlyCauchySeries : ∀ {ℓ}
  (X : Type ℓ) (a b : X → RealSequence) →
  UniformlyEventuallyEqualPartialSums X a b →
  UniformlyCauchySeries X a →
  UniformlyCauchySeries X b
uniformlyEventuallyEqualPartialSumsPresUniformlyCauchySeries
  X a b eventually-equal a-uniform ε =
  PT.rec2
    squash₁
    transport-tail
    eventually-equal
    (a-uniform ε)
  where
  transport-tail :
    (Σ[ K ∈ ℕ ]
      (∀ x n → K ℕ.≤ n →
        partialSum (a x) n ≡ partialSum (b x) n)) →
    UniformCauchyTail X a ε →
    ∥ UniformCauchyTail X b ε ∥₁
  transport-tail (K , equal) (N , close) =
    ∣ Nat.max K N
    , (λ x m n max≤m max≤n →
        subst2 (Real.Base._≈ᶜ[ ε ]_)
          (equal x m
            (ℕ.≤-trans
              (ℕ.left-≤-max {m = K} {n = N}) max≤m))
          (equal x n
            (ℕ.≤-trans
              (ℕ.left-≤-max {m = K} {n = N}) max≤n))
          (close x m n
            (ℕ.≤-trans
              (ℕ.right-≤-max {n = N} {m = K}) max≤m)
            (ℕ.≤-trans
              (ℕ.right-≤-max {n = N} {m = K}) max≤n)))
    ∣₁


-- Uniform Cauchy families form an additive group pointwise.  Addition uses
-- one maximum of the two merely supplied half-radius cutoffs, so it does not
-- manufacture a modulus function.

addUniformlyCauchySeries : ∀ {ℓ} (X : Type ℓ)
  (a b : X → RealSequence) →
  UniformlyCauchySeries X a →
  UniformlyCauchySeries X b →
  UniformlyCauchySeries X
    (λ x n → a x n Add.+ b x n)
addUniformlyCauchySeries X a b a-uniform b-uniform ε =
  PT.map2 combine (a-uniform (ε /2₊)) (b-uniform (ε /2₊))
  where
  combine :
    UniformCauchyTail X a (ε /2₊) →
    UniformCauchyTail X b (ε /2₊) →
    UniformCauchyTail X (λ x n → a x n Add.+ b x n) ε
  combine (A , close-a) (B , close-b) =
    Nat.max A B , λ x m n max≤m max≤n →
      subst2 (Real.Base._≈ᶜ[ ε ]_)
        (sym (partialSum-add (a x) (b x) m))
        (sym (partialSum-add (a x) (b x) n))
        (subst
          (λ radius →
            (partialSum (a x) m Add.+ partialSum (b x) m)
              Real.Base.≈ᶜ[ radius ]
            (partialSum (a x) n Add.+ partialSum (b x) n))
          (ℚ₊≡ (/2+/2≡id (fst ε)))
          (add-pres≈
            (partialSum (a x) m) (partialSum (a x) n)
            (partialSum (b x) m) (partialSum (b x) n)
            (ε /2₊) (ε /2₊)
            (close-a x m n
              (ℕ.≤-trans
                (ℕ.left-≤-max {m = A} {n = B}) max≤m)
              (ℕ.≤-trans
                (ℕ.left-≤-max {m = A} {n = B}) max≤n))
            (close-b x m n
              (ℕ.≤-trans
                (ℕ.right-≤-max {n = B} {m = A}) max≤m)
              (ℕ.≤-trans
                (ℕ.right-≤-max {n = B} {m = A}) max≤n))))


negUniformlyCauchySeries : ∀ {ℓ} (X : Type ℓ)
  (terms : X → RealSequence) →
  UniformlyCauchySeries X terms →
  UniformlyCauchySeries X (λ x → Neg.-_ ∘ terms x)
negUniformlyCauchySeries X terms uniform ε =
  PT.map negate-tail (uniform ε)
  where
  negate-tail : UniformCauchyTail X terms ε →
    UniformCauchyTail X (λ x → Neg.-_ ∘ terms x) ε
  negate-tail (N , close) =
    N , λ x m n N≤m N≤n →
      subst2 (Real.Base._≈ᶜ[ ε ]_)
        (sym (partialSum-neg (terms x) m))
        (sym (partialSum-neg (terms x) n))
        (Neg.neg-pres≈
          (partialSum (terms x) m)
          (partialSum (terms x) n) ε
          (close x m n N≤m N≤n))


-- Scaling by an arbitrary completed real still preserves a common tail.  A
-- single merely existing rational bound for the scalar is opened separately
-- at the requested output radius; no bound or modulus is selected globally.

scaleUniformlyCauchySeries : ∀ {ℓ} (X : Type ℓ)
  (c : Real.ℝ) (terms : X → RealSequence) →
  UniformlyCauchySeries X terms →
  UniformlyCauchySeries X (λ x → scaleSeries c (terms x))
scaleUniformlyCauchySeries X c terms uniform ε =
  PT.rec squash₁ bounded-scale (∃rationalBound c)
  where
  bounded-scale : RationalBound c →
    ∥ UniformCauchyTail X (λ x → scaleSeries c (terms x)) ε ∥₁
  bounded-scale (B , absc≤B) =
    PT.map scale-tail (uniform (ε ₊／₊ B))
    where
    scale-tail : UniformCauchyTail X terms (ε ₊／₊ B) →
      UniformCauchyTail X (λ x → scaleSeries c (terms x)) ε
    scale-tail (N , close) =
      N , λ x m n N≤m N≤n →
        subst2 (Real.Base._≈ᶜ[ ε ]_)
          (sym (partialSum-scale c (terms x) m))
          (sym (partialSum-scale c (terms x) n))
          (subst
            (λ radius →
              (c Mul.· partialSum (terms x) m)
                Real.Base.≈ᶜ[ radius ]
              (c Mul.· partialSum (terms x) n))
            (ℚ₊≡ (·／ B ε))
            (mulIsLipschitzLeftAtBound B c absc≤B
              .IsLipschitzWith.pres≈
                (partialSum (terms x) m)
                (partialSum (terms x) n)
                (ε ₊／₊ B)
                (close x m n N≤m N≤n)))


subUniformlyCauchySeries : ∀ {ℓ} (X : Type ℓ)
  (a b : X → RealSequence) →
  UniformlyCauchySeries X a →
  UniformlyCauchySeries X b →
  UniformlyCauchySeries X
    (λ x n → a x n Group.- b x n)
subUniformlyCauchySeries X a b a-uniform b-uniform =
  addUniformlyCauchySeries X a (λ x → Neg.-_ ∘ b x)
    a-uniform (negUniformlyCauchySeries X b b-uniform)
