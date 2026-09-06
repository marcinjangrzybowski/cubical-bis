module Cubical.HITs.CauchyReals.Circle.UniformGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast using (ℤ; pos)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring using (module Rℝ)
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Trigonometry.Pi using (x²≤1→∣x∣≤1)
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Group
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.Winding.Continuity
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open CategoryStructures using (_∘UC_)

private
  module D = PremetricStr (snd distCirclePremetricSpace)

opaque
  circle-X-bound : (p : distCircle) → absᵣ (fst (fst p)) ≤ᵣ 1
  circle-X-bound ((x , y) , norm) = x²≤1→∣x∣≤1 x
    (isTrans≡≤ᵣ _ _ _ (x^²=x·x x)
      (isTrans≤≡ᵣ _ _ _
        (isTrans≡≤ᵣ _ _ _ (sym (+IdR (x ·ᵣ x)))
          (≤ᵣ-o+ 0 (y ·ᵣ y) (x ·ᵣ x)
            (isTrans≤≡ᵣ _ _ _ (0≤ᵣx² y) (x^²=x·x y)))) norm))

  circle-Y-bound : (p : distCircle) → absᵣ (snd (fst p)) ≤ᵣ 1
  circle-Y-bound ((x , y) , norm) =
    circle-X-bound ((y , x) , (+ᵣComm _ _ ∙ norm))

  bounded-scale : ∀ a → absᵣ a ≤ᵣ 1 → ∀ x y ε → x ∼[ ε ] y →
    (x ·ᵣ a) ∼[ ε ] (y ·ᵣ a)
  bounded-scale a bound x y ε close = invEq (∼≃abs<ε _ _ ε)
    (isTrans≡<ᵣ _ _ _
      (cong absᵣ (sym (Rℝ.·DistL- x y a)) ∙ ·absᵣ (x -ᵣ y) a)
      (isTrans≤<ᵣ _ _ _
        (isTrans≤≡ᵣ _ _ _
          (≤ᵣ-o·ᵣ (absᵣ a) 1 (absᵣ (x -ᵣ y)) (0≤absᵣ _) bound)
          (Rℝ.·IdR _))
        (equivFun (∼≃abs<ε x y ε) close)))

  bounded-product : ∀ a b c d → absᵣ b ≤ᵣ 1 → absᵣ c ≤ᵣ 1 →
    ∀ ε → a ∼[ ε ] c → b ∼[ ε ] d →
    (a ·ᵣ b) ∼[ ε +₊ ε ] (c ·ᵣ d)
  bounded-product a b c d bb cb ε ac bd = triangle∼
    (bounded-scale b bb a c ε ac)
    (subst2 (λ x y → x ∼[ ε ] y) (·ᵣComm b c) (·ᵣComm d c)
      (bounded-scale c cb b d ε bd))

opaque
  circleAddModulus : ℚ₊ → ℚ₊
  circleAddModulus ε = ε /4₊

opaque
  unfolding circleAddModulus
  circle-add-close : (p q r s : distCircle) (ε : ℚ₊) →
    p D.≈[ circleAddModulus ε ] r → q D.≈[ circleAddModulus ε ] s → circle+ p q D.≈[ ε ] circle+ r s
  circle-add-close p q r s ε pr qs =
    ∼→≈ℝ (fst (fst (circle+ p q))) (fst (fst (circle+ r s))) ε
      (subst2 (λ x y → x ∼[ ε ] y) (sym (circle+-X p q)) (sym (circle+-X r s))
      (subst∼ {0<ε = snd ((ρ +₊ ρ) +₊ (ρ +₊ ρ))} {0<ε' = snd ε} ℚ!
        (+ᵣ-ne₂ (ρ +₊ ρ) (ρ +₊ ρ) xx
          (-ᵣ-nonExpanding _ _ (ρ +₊ ρ) yy)))) ,
    ∼→≈ℝ (snd (fst (circle+ p q))) (snd (fst (circle+ r s))) ε
      (subst2 (λ x y → x ∼[ ε ] y) (sym (circle+-Y p q)) (sym (circle+-Y r s))
      (subst∼ {0<ε = snd ((ρ +₊ ρ) +₊ (ρ +₊ ρ))} {0<ε' = snd ε} ℚ!
        (+ᵣ-ne₂ (ρ +₊ ρ) (ρ +₊ ρ) xy yx)))
    where
    ρ : ℚ₊
    ρ = ε /4₊
    xx : (fst (fst p) ·ᵣ fst (fst q)) ∼[ ρ +₊ ρ ] (fst (fst r) ·ᵣ fst (fst s))
    xx = bounded-product _ _ _ _ (circle-X-bound q) (circle-X-bound r) ρ
      (≈ℝ→∼ _ _ ρ (fst pr)) (≈ℝ→∼ _ _ ρ (fst qs))
    yy : (snd (fst p) ·ᵣ snd (fst q)) ∼[ ρ +₊ ρ ] (snd (fst r) ·ᵣ snd (fst s))
    yy = bounded-product _ _ _ _ (circle-Y-bound q) (circle-Y-bound r) ρ
      (≈ℝ→∼ _ _ ρ (snd pr)) (≈ℝ→∼ _ _ ρ (snd qs))
    xy : (fst (fst p) ·ᵣ snd (fst q)) ∼[ ρ +₊ ρ ] (fst (fst r) ·ᵣ snd (fst s))
    xy = bounded-product _ _ _ _ (circle-Y-bound q) (circle-X-bound r) ρ
      (≈ℝ→∼ _ _ ρ (fst pr)) (≈ℝ→∼ _ _ ρ (snd qs))
    yx : (snd (fst p) ·ᵣ fst (fst q)) ∼[ ρ +₊ ρ ] (snd (fst r) ·ᵣ fst (fst s))
    yx = bounded-product _ _ _ _ (circle-X-bound q) (circle-Y-bound r) ρ
      (≈ℝ→∼ _ _ ρ (snd pr)) (≈ℝ→∼ _ _ ρ (fst qs))

-- Pointwise operations are proved for an arbitrary domain premetric.
module _ {ℓ ℓ'} {M : PremetricSpace ℓ ℓ'} where
  private
    module P = PremetricStr (snd M)

  addDistCircleUC : UC[ M , distCirclePremetricSpace ] → UC[ M , distCirclePremetricSpace ] →
    UC[ M , distCirclePremetricSpace ]
  addDistCircleUC f g = (λ x → circle+ (fst f x) (fst g x)) , PT.map2 combine (snd f) (snd g)
    where
    combine :
      (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd M) (fst f) (snd distCirclePremetricSpace) μ) →
      (Σ[ ν ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd M) (fst g) (snd distCirclePremetricSpace) ν) →
      Σ[ κ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith (snd M)
        (λ x → circle+ (fst f x) (fst g x)) (snd distCirclePremetricSpace) κ
    combine (μ , fc) (ν , gc) = (λ ε → min₊ (μ (circleAddModulus ε)) (ν (circleAddModulus ε))) , preserves
      where
      preserves : IsUniformlyContinuousWith (snd M)
        (λ x → circle+ (fst f x) (fst g x)) (snd distCirclePremetricSpace)
        (λ ε → min₊ (μ (circleAddModulus ε)) (ν (circleAddModulus ε)))
      IsUniformlyContinuousWith.pres≈ preserves x y ε close =
        circle-add-close (fst f x) (fst g x) (fst f y) (fst g y) ε
          (IsUniformlyContinuousWith.pres≈ fc x y (circleAddModulus ε)
            (P.isMonotone≈≤ x y _ (μ (circleAddModulus ε))
              (min₊≤L (μ (circleAddModulus ε)) (ν (circleAddModulus ε))) close))
          (IsUniformlyContinuousWith.pres≈ gc x y (circleAddModulus ε)
            (P.isMonotone≈≤ x y _ (ν (circleAddModulus ε))
              (min₊≤R (μ (circleAddModulus ε)) (ν (circleAddModulus ε))) close))

distCircleAddUC : UC[
  PremetricProduct distCirclePremetricSpace distCirclePremetricSpace , distCirclePremetricSpace ]
distCircleAddUC = addDistCircleUC productFstUC productSndUC

opaque
  unfolding circleNeg
  circle-neg-X : ∀ p → fst (fst (circleNeg p)) ≡ fst (fst p)
  circle-neg-X p = refl
  circle-neg-Y : ∀ p → snd (fst (circleNeg p)) ≡ -ᵣ snd (fst p)
  circle-neg-Y p = refl

opaque
  circle-neg-close : ∀ p q ε → p D.≈[ ε ] q → circleNeg p D.≈[ ε ] circleNeg q
  circle-neg-close p q ε close =
    subst2 (λ x y → x ≈ℝ[ ε ] y) (sym (circle-neg-X p)) (sym (circle-neg-X q)) (fst close) ,
    subst2 (λ x y → x ≈ℝ[ ε ] y) (sym (circle-neg-Y p)) (sym (circle-neg-Y q))
      (∼→≈ℝ (-ᵣ snd (fst p)) (-ᵣ snd (fst q)) ε
        (-ᵣ-nonExpanding _ _ ε (≈ℝ→∼ _ _ ε (snd close))))

circle-neg-nonexpanding : IsNonExpanding (snd distCirclePremetricSpace)
  circleNeg (snd distCirclePremetricSpace)
circle-neg-nonexpanding = isnonexpanding circle-neg-close

distCircleNegUC : UC[ distCirclePremetricSpace , distCirclePremetricSpace ]
distCircleNegUC = NE→UC (circleNeg , circle-neg-nonexpanding)

opaque
  cartesianEquivalence : Circle ≃ distCircle
  cartesianEquivalence = Circle≃distCircle

  cartesianEquivalence-β : ∀ p → equivFun cartesianEquivalence p ≡ Circle→distCircle p
  cartesianEquivalence-β p = refl

opaque
  fromCartesian : distCircle → Circle
  fromCartesian = invEq cartesianEquivalence

  to-fromCartesian : ∀ p → Circle→distCircle (fromCartesian p) ≡ p
  to-fromCartesian p = sym (cartesianEquivalence-β (fromCartesian p)) ∙ secEq cartesianEquivalence p

  from-toCartesian : ∀ p → fromCartesian (Circle→distCircle p) ≡ p
  from-toCartesian p = cong (invEq cartesianEquivalence) (sym (cartesianEquivalence-β p))
    ∙ retEq cartesianEquivalence p

private
  fromCartesian-close : ∀ p q ε → p D.≈[ ε ] q →
    PremetricStr._≈[_]_ (snd CirclePremetricSpace) (fromCartesian p) ε (fromCartesian q)
  fromCartesian-close p q ε close = subst2 (λ x y → x D.≈[ ε ] y)
    (sym (to-fromCartesian p)) (sym (to-fromCartesian q)) close

fromCartesianUC : UC[ distCirclePremetricSpace , CirclePremetricSpace ]
fromCartesianUC = NE→UC (fromCartesian , isnonexpanding fromCartesian-close)

module _ {ℓ ℓ'} {M : PremetricSpace ℓ ℓ'} where
  addCircleUC : UC[ M , CirclePremetricSpace ] → UC[ M , CirclePremetricSpace ] →
    UC[ M , CirclePremetricSpace ]
  addCircleUC f g = fromCartesianUC ∘UC
    addDistCircleUC (Circle→distCircleUC ∘UC f) (Circle→distCircleUC ∘UC g)

  negCircleUC : UC[ M , CirclePremetricSpace ] → UC[ M , CirclePremetricSpace ]
  negCircleUC f = fromCartesianUC ∘UC (distCircleNegUC ∘UC (Circle→distCircleUC ∘UC f))

  addCircle-image : (f g : UC[ M , CirclePremetricSpace ]) → ∀ x →
    Circle→distCircle (fst (addCircleUC f g) x) ≡
    Circle→distCircle (fst f x) ℝS¹.+ Circle→distCircle (fst g x)
  addCircle-image f g x = to-fromCartesian _

  negCircle-image : (f : UC[ M , CirclePremetricSpace ]) → ∀ x →
    Circle→distCircle (fst (negCircleUC f) x) ≡ ℝS¹.- Circle→distCircle (fst f x)
  negCircle-image f x = to-fromCartesian _

constantUC : ∀ {ℓ ℓ' ℓN ℓN'} {M : PremetricSpace ℓ ℓ'} {N : PremetricSpace ℓN ℓN'} →
  fst N → UC[ M , N ]
constantUC {N = N} c = (λ _ → c) , ∣ idfun ℚ₊ ,
  isuniformlycontinuouswith (λ x y ε _ → PremetricStr.isRefl≈ (snd N) c ε) ∣₁
