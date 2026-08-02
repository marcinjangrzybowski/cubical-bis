module Cubical.HITs.CauchyRealsP.Algebra.Order.Clamp where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Lattice
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue

open import Cubical.Relation.Premetric.Mappings

clampInterval : ℝ → ℝ → ℝ → ℝ
clampInterval a b x =
  minℝ (maxℝ a x) b

clampIntervalPres∼ : ∀ a b x y ε →
  x ∼[ ε ] y →
  clampInterval a b x ∼[ ε ] clampInterval a b y
clampIntervalPres∼ a b x y ε x∼y =
  minPres∼₁
    (maxℝ a x) (maxℝ a y) b ε
    (maxPres∼₂ a x y ε x∼y)

clampIntervalIsNonExpanding : ∀ a b →
  IsNonExpanding
    (snd ℝPremetricSpace)
    (clampInterval a b)
    (snd ℝPremetricSpace)
clampIntervalIsNonExpanding a b
  .IsNonExpanding.pres≈ x y ε =
    clampIntervalPres∼ a b x y ε

clampIntervalLowerBound : ∀ a b →
  a ≤ℝ b →
  ∀ x → a ≤ℝ clampInterval a b x
clampIntervalLowerBound a b a≤b x =
  ≤min
    a (maxℝ a x) b
    (left≤max a x) a≤b

clampIntervalUpperBound : ∀ a b x →
  clampInterval a b x ≤ℝ b
clampIntervalUpperBound a b x =
  min≤right (maxℝ a x) b

clampIntervalFixpoint : ∀ a b x →
  a ≤ℝ x →
  x ≤ℝ b →
  clampInterval a b x ≡ x
clampIntervalFixpoint a b x a≤x x≤b =
  cong (λ u → minℝ u b)
    (maxOf≤ a x a≤x)
  ∙ minOf≤ x b x≤b

clampIntervalIdem : ∀ a b →
  a ≤ℝ b →
  ∀ x →
  clampInterval a b (clampInterval a b x)
    ≡ clampInterval a b x
clampIntervalIdem a b a≤b x =
  clampIntervalFixpoint a b (clampInterval a b x)
    (clampIntervalLowerBound a b a≤b x)
    (clampIntervalUpperBound a b x)

absBound→symmetricIntervalBounds : ∀ radius x →
  absℝ x ≤ℝ radius →
  ((- radius) ≤ℝ x) × (x ≤ℝ radius)
absBound→symmetricIntervalBounds radius x absx≤radius =
  lower-bound , upper-bound
  where
  lower-bound : (- radius) ≤ℝ x
  lower-bound =
    subst
      ((- radius) ≤ℝ_)
      (negInvol x)
      (≤ℝ-neg
        (- x) radius
        (≤ℝ-trans
          (- x) (absℝ x) radius
          (negLeAbs x) absx≤radius))

  upper-bound : x ≤ℝ radius
  upper-bound =
    ≤ℝ-trans x (absℝ x) radius
      (leAbs x) absx≤radius

symmetricIntervalBounds→absBound : ∀ radius x →
  (- radius) ≤ℝ x →
  x ≤ℝ radius →
  absℝ x ≤ℝ radius
symmetricIntervalBounds→absBound radius x lower-bound upper-bound =
  subst
    (_≤ℝ radius)
    (sym (absAsMax x))
    (max≤
      x (- x) radius
      upper-bound
      (subst
        ((- x) ≤ℝ_)
        (negInvol radius)
        (≤ℝ-neg (- radius) x lower-bound)))

symmetricIntervalLower≤Upper : ∀ radius →
  0 ≤ℝ radius →
  (- radius) ≤ℝ radius
symmetricIntervalLower≤Upper radius 0≤radius =
  ≤ℝ-trans (- radius) 0 radius
    (subst
      ((- radius) ≤ℝ_)
      negZero
      (≤ℝ-neg 0 radius 0≤radius))
    0≤radius

clampSymmetricAbsBound : ∀ radius →
  0 ≤ℝ radius →
  ∀ x →
  absℝ (clampInterval (- radius) radius x) ≤ℝ radius
clampSymmetricAbsBound radius 0≤radius x =
  symmetricIntervalBounds→absBound
    radius (clampInterval (- radius) radius x)
    (clampIntervalLowerBound
      (- radius) radius
      (symmetricIntervalLower≤Upper radius 0≤radius)
      x)
    (clampIntervalUpperBound (- radius) radius x)

clampSymmetricFixpointFromAbs : ∀ radius x →
  absℝ x ≤ℝ radius →
  clampInterval (- radius) radius x ≡ x
clampSymmetricFixpointFromAbs radius x absx≤radius =
  clampIntervalFixpoint (- radius) radius x
    (fst (absBound→symmetricIntervalBounds radius x absx≤radius))
    (snd (absBound→symmetricIntervalBounds radius x absx≤radius))

clampℝ : ℚ₊ → ℝ → ℝ
clampℝ B x =
  minℝ (maxℝ (rat (ℚ.- fst B)) x) (rat (fst B))

clamp-rat : ∀ B q →
  clampℝ B (rat q) ≡ rat (ℚ.clamp (ℚ.- fst B) (fst B) q)
clamp-rat B q =
  cong (λ u → minℝ u (rat (fst B)))
    (max-rat (ℚ.- fst B) q)
  ∙ min-rat (ℚ.max (ℚ.- fst B) q) (fst B)

clampPres∼ : ∀ B x y ε →
  x ∼[ ε ] y → clampℝ B x ∼[ ε ] clampℝ B y
clampPres∼ B x y ε x∼y =
  minPres∼₁
    (maxℝ (rat (ℚ.- fst B)) x)
    (maxℝ (rat (ℚ.- fst B)) y)
    (rat (fst B)) ε
    (maxPres∼₂ (rat (ℚ.- fst B)) x y ε x∼y)

clampIsNonExpanding : ∀ B →
  IsNonExpanding
    (snd ℝPremetricSpace) (clampℝ B)
    (snd ℝPremetricSpace)
clampIsNonExpanding B
  .IsNonExpanding.pres≈ x y ε =
    clampPres∼ B x y ε

clampLower≤Upper : ∀ B →
  rat (ℚ.- fst B) ≤ℝ rat (fst B)
clampLower≤Upper B =
  ≤ℚ→≤ℝ
    (ℚ.- fst B) (fst B)
    (ℚ.isTrans≤
      (ℚ.- fst B) 0 (fst B)
      (-ℚ₊≤0 B) (ℚ.0≤ℚ₊ B))

clampLowerBound : ∀ B x →
  rat (ℚ.- fst B) ≤ℝ clampℝ B x
clampLowerBound B x =
  ≤min
    (rat (ℚ.- fst B))
    (maxℝ (rat (ℚ.- fst B)) x)
    (rat (fst B))
    (left≤max (rat (ℚ.- fst B)) x)
    (clampLower≤Upper B)

clampUpperBound : ∀ B x →
  clampℝ B x ≤ℝ rat (fst B)
clampUpperBound B x =
  min≤right
    (maxℝ (rat (ℚ.- fst B)) x)
    (rat (fst B))

clampFixpoint : ∀ B x →
  rat (ℚ.- fst B) ≤ℝ x →
  x ≤ℝ rat (fst B) →
  clampℝ B x ≡ x
clampFixpoint B x lower≤x x≤upper =
  cong (λ u → minℝ u (rat (fst B)))
    (maxOf≤ (rat (ℚ.- fst B)) x lower≤x)
  ∙ minOf≤ x (rat (fst B)) x≤upper

absBound→clampBounds : ∀ (B : ℚ₊) (x : ℝ) →
  absℝ x ≤ℝ rat (fst B) →
  (rat (ℚ.- fst B) ≤ℝ x) ×
  (x ≤ℝ rat (fst B))
absBound→clampBounds B x absx≤B = lowerProof , upperProof
  where
  lowerProof : rat (ℚ.- fst B) ≤ℝ x
  lowerProof =
    subst2 _≤ℝ_
      (neg-rat (fst B))
      (negInvol x)
      (≤ℝ-neg
        (- x) (rat (fst B))
        (≤ℝ-trans
          (- x) (absℝ x) (rat (fst B))
          (negLeAbs x) absx≤B))

  upperProof : x ≤ℝ rat (fst B)
  upperProof =
    ≤ℝ-trans
      x (absℝ x) (rat (fst B))
      (leAbs x) absx≤B

clampFixpointFromAbs : ∀ (B : ℚ₊) (x : ℝ) →
  absℝ x ≤ℝ rat (fst B) →
  clampℝ B x ≡ x
clampFixpointFromAbs B x absx≤B =
  clampFixpoint B x
    (fst (absBound→clampBounds B x absx≤B))
    (snd (absBound→clampBounds B x absx≤B))

clampIdem : ∀ B x → clampℝ B (clampℝ B x) ≡ clampℝ B x
clampIdem B x =
  clampFixpoint B (clampℝ B x)
    (clampLowerBound B x)
    (clampUpperBound B x)

clampAbsBound : ∀ B x →
  absℝ (clampℝ B x) ≤ℝ rat (fst B)
clampAbsBound B x =
  subst (_≤ℝ rat (fst B))
    (sym (absAsMax (clampℝ B x)))
    (max≤
      (clampℝ B x) (- clampℝ B x) (rat (fst B))
      (clampUpperBound B x)
      (subst
        ((- clampℝ B x) ≤ℝ_)
        (neg-rat (ℚ.- fst B)
        ∙ cong rat (ℚ.-Invol (fst B)))
        (≤ℝ-neg
          (rat (ℚ.- fst B)) (clampℝ B x)
          (clampLowerBound B x))))
