module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

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
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition.Mesh
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral


-- Pointwise replacement is exact, hence does not consume any error budget.

riemannIntegral-cong : ∀ {a b f g value} →
  (∀ x → f x ≡ g x) →
  IsRiemannIntegral {a} {b} f value →
  IsRiemannIntegral {a} {b} g value
riemannIntegral-cong {f = f} {g = g} {value = value}
  f≡g integral ε =
  PT.map
    (λ { (δ , close) →
      δ , λ tagged mesh →
        subst
          (λ z → z Real.Base.≈ᶜ[ ε ] value)
          (riemannSum-cong tagged f g
            (λ i → f≡g (TaggedPartition[_,_].tags tagged i)))
          (close tagged mesh) })
    (integral ε)


riemannIntegral-constant : ∀ {a b} c →
  IsRiemannIntegral {a} {b}
    (λ _ → c)
    ((b Group.- a) Mul.· c)
riemannIntegral-constant {a} {b} c ε =
  ∣ ε , (λ tagged _ →
    subst
      (λ z → z Real.Base.≈ᶜ[ ε ] ((b Group.- a) Mul.· c))
      (sym (riemannSum-constant tagged c))
      (Real.Base.isRefl≈ᶜ ((b Group.- a) Mul.· c) ε)) ∣₁


-- The two input mesh radii remain independent until this single requested
-- output radius is handled.  Taking their rational minimum is finite choice,
-- not the countable choice that a global modulus would require.

riemannIntegral-add : ∀ {a b f g integral-f integral-g} →
  IsRiemannIntegral {a} {b} f integral-f →
  IsRiemannIntegral {a} {b} g integral-g →
  IsRiemannIntegral {a} {b}
    (λ x → f x Add.+ g x)
    (integral-f Add.+ integral-g)
riemannIntegral-add {f = f} {g = g}
  {integral-f = integral-f} {integral-g = integral-g}
  f-integral g-integral ε =
  PT.rec squash₁ use-f-radius (f-integral (ε /2₊))
  where
  use-f-radius : _ → _
  use-f-radius (δf , f-close) =
    PT.map
      (λ { (δg , g-close) →
        min₊ δf δg , λ tagged mesh →
          subst
            (λ z → z Real.Base.≈ᶜ[ ε ]
              (integral-f Add.+ integral-g))
            (sym (riemannSum-add tagged f g))
            (subst
              (λ ρ →
                (riemannSum tagged f Add.+ riemannSum tagged g)
                  Real.Base.≈ᶜ[ ρ ]
                (integral-f Add.+ integral-g))
              (ℚ₊≡ (/2+/2≡id (fst ε)))
              (add-pres≈
                (riemannSum tagged f) integral-f
                (riemannSum tagged g) integral-g
                (ε /2₊) (ε /2₊)
                (f-close tagged
                  (meshBelowMonotone
                    (TaggedPartition[_,_].partition tagged)
                    (min₊ δf δg) δf
                    (min₊≤L δf δg) mesh))
                (g-close tagged
                  (meshBelowMonotone
                    (TaggedPartition[_,_].partition tagged)
                    (min₊ δf δg) δg
                    (min₊≤R δf δg) mesh)))) })
      (g-integral (ε /2₊))


riemannIntegral-neg : ∀ {a b f integral-f} →
  IsRiemannIntegral {a} {b} f integral-f →
  IsRiemannIntegral {a} {b}
    (λ x → Neg.- f x)
    (Neg.- integral-f)
riemannIntegral-neg {f = f} {integral-f = integral-f}
  f-integral ε =
  PT.map
    (λ { (δ , close) →
      δ , λ tagged mesh →
        subst
          (λ z → z Real.Base.≈ᶜ[ ε ] (Neg.- integral-f))
          (sym (riemannSum-neg tagged f))
          (Neg.neg-pres≈
            (riemannSum tagged f) integral-f ε
            (close tagged mesh)) })
    (f-integral ε)


riemannIntegral-sub : ∀ {a b f g integral-f integral-g} →
  IsRiemannIntegral {a} {b} f integral-f →
  IsRiemannIntegral {a} {b} g integral-g →
  IsRiemannIntegral {a} {b}
    (λ x → f x Group.- g x)
    (integral-f Group.- integral-g)
riemannIntegral-sub {a} {b} {f = f} {g = g}
  {integral-f = integral-f} {integral-g = integral-g}
  f-integral g-integral =
  riemannIntegral-add
    {a = a} {b = b}
    {f = f} {g = λ x → Neg.- g x}
    {integral-f = integral-f} {integral-g = Neg.- integral-g}
    f-integral
    (riemannIntegral-neg
      {a = a} {b = b} {f = g} {integral-f = integral-g}
      g-integral)


-- Mere integrability is closed under the additive operations.  These maps
-- combine only finitely many truncated witnesses, so they do not introduce a
-- modulus-selection principle.

merelyRiemannIntegrable-constant : ∀ {a b} c →
  MerelyRiemannIntegrable {a} {b} (λ _ → c)
merelyRiemannIntegrable-constant {a} {b} c =
  ∣ (b Group.- a) Mul.· c , riemannIntegral-constant c ∣₁


merelyRiemannIntegrable-add : ∀ {a b f g} →
  MerelyRiemannIntegrable {a} {b} f →
  MerelyRiemannIntegrable {a} {b} g →
  MerelyRiemannIntegrable {a} {b} (λ x → f x Add.+ g x)
merelyRiemannIntegrable-add {a} {b} {f} {g} =
  PT.map2 λ { (integral-f , f-proof) (integral-g , g-proof) →
    integral-f Add.+ integral-g ,
    riemannIntegral-add
      {a = a} {b = b} {f = f} {g = g}
      {integral-f = integral-f} {integral-g = integral-g}
      f-proof g-proof }


merelyRiemannIntegrable-neg : ∀ {a b f} →
  MerelyRiemannIntegrable {a} {b} f →
  MerelyRiemannIntegrable {a} {b} (λ x → Neg.- f x)
merelyRiemannIntegrable-neg {a} {b} {f} =
  PT.map λ { (integral-f , f-proof) →
    Neg.- integral-f ,
    riemannIntegral-neg
      {a = a} {b = b} {f = f} {integral-f = integral-f}
      f-proof }


merelyRiemannIntegrable-sub : ∀ {a b f g} →
  MerelyRiemannIntegrable {a} {b} f →
  MerelyRiemannIntegrable {a} {b} g →
  MerelyRiemannIntegrable {a} {b} (λ x → f x Group.- g x)
merelyRiemannIntegrable-sub {a} {b} {f} {g} f-integrable g-integrable =
  merelyRiemannIntegrable-add
    {a = a} {b = b} {f = f} {g = λ x → Neg.- g x}
    f-integrable
    (merelyRiemannIntegrable-neg
      {a = a} {b = b} {f = g} g-integrable)


-- After fixing any vanishing-mesh scheme, the extracted definite integral is
-- genuinely additive.  The proof compares two Riemann-integral witnesses by
-- uniqueness, rather than exposing the representatives hidden in either
-- integrability assumption.

integralValue-add : ∀ {a b f g}
  (partitions : ℕ → TaggedPartition[ a , b ])
  (mesh→zero : HasVanishingMesh partitions)
  (f-integrable : MerelyRiemannIntegrable {a} {b} f)
  (g-integrable : MerelyRiemannIntegrable {a} {b} g) →
  integralValue
    {a = a} {b = b} {f = λ x → f x Add.+ g x}
    partitions mesh→zero
    (merelyRiemannIntegrable-add
      {a = a} {b = b} {f = f} {g = g}
      f-integrable g-integrable)
  ≡
  integralValue {a = a} {b = b} {f = f}
    partitions mesh→zero f-integrable
  Add.+
  integralValue {a = a} {b = b} {f = g}
    partitions mesh→zero g-integrable
integralValue-add {a} {b} {f} {g}
  partitions mesh→zero f-integrable g-integrable =
  riemannIntegralUniqueAlongVanishingMesh
    {a = a} {b = b} {f = λ x → f x Add.+ g x}
    {x = integralValue
      {a = a} {b = b} {f = λ x → f x Add.+ g x}
      partitions mesh→zero
      (merelyRiemannIntegrable-add
        {a = a} {b = b} {f = f} {g = g}
        f-integrable g-integrable)}
    {y = integralValue {a = a} {b = b} {f = f}
      partitions mesh→zero f-integrable Add.+
      integralValue {a = a} {b = b} {f = g}
      partitions mesh→zero g-integrable}
    partitions mesh→zero
    (integralValueIsRiemannIntegral
      {a = a} {b = b} {f = λ x → f x Add.+ g x}
      partitions mesh→zero
      (merelyRiemannIntegrable-add
        {a = a} {b = b} {f = f} {g = g}
        f-integrable g-integrable))
    (riemannIntegral-add
      {a = a} {b = b} {f = f} {g = g}
      {integral-f = integralValue
        {a = a} {b = b} {f = f}
        partitions mesh→zero f-integrable}
      {integral-g = integralValue
        {a = a} {b = b} {f = g}
        partitions mesh→zero g-integrable}
      (integralValueIsRiemannIntegral
        {a = a} {b = b} {f = f}
        partitions mesh→zero f-integrable)
      (integralValueIsRiemannIntegral
        {a = a} {b = b} {f = g}
        partitions mesh→zero g-integrable))
