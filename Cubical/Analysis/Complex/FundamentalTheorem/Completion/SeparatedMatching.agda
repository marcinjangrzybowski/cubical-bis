open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Relation.Premetric.Base

module Cubical.Analysis.Complex.FundamentalTheorem.Completion.SeparatedMatching
  (M : PremetricSpace ℓ-zero ℓ-zero) (n : ℕ) where

-- Separate the finite matching pseudometric before completing it.
-- Equality means matching at every positive radius; it does not assert
-- that one exact permutation can be selected from those matchings.

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Data.Vec using (Vec)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; _+₊_; _<₊_; [_-₊_]⟨_⟩; minusPlus₊; ℚ₊≡)
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.FiniteMatching M

AllMatching : Vec (fst M) n → Vec (fst M) n → Type₀
AllMatching xs ys = ∀ ε → Match xs ε ys

-- Roundedness absorbs the arbitrarily small cost of replacing an endpoint.
replace-left : ∀ xs xs′ ys ε → AllMatching xs xs′ → Match xs ε ys → Match xs′ ε ys
replace-left xs xs′ ys ε same close = PT.rec PT.isPropPropTrunc tighten (match-rounded xs ys ε close)
  where
  tighten : (Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) × Match xs δ ys) → Match xs′ ε ys
  tighten (δ , below , smaller) =
    subst (λ radius → Match xs′ radius ys) (ℚ₊≡ (minusPlus₊ ε δ))
      (match-triangle xs′ xs ys [ ε -₊ δ ]⟨ below ⟩ δ
        (match-sym xs xs′ [ ε -₊ δ ]⟨ below ⟩ (same [ ε -₊ δ ]⟨ below ⟩)) smaller)

replace-right : ∀ xs ys ys′ ε → AllMatching ys ys′ → Match xs ε ys → Match xs ε ys′
replace-right xs ys ys′ ε same close = match-sym ys′ xs ε
  (replace-left ys ys′ xs ε same (match-sym xs ys ε close))

Configuration : Type₀
Configuration = Vec (fst M) n SQ./ AllMatching

insert : Vec (fst M) n → Configuration
insert = SQ.[_]

opaque
  closeProp : ℚ₊ → Configuration → Configuration → hProp ℓ-zero
  closeProp ε = SQ.rec2 isSetHProp
    (λ xs ys → Match xs ε ys , PT.isPropPropTrunc)
    (λ xs xs′ ys same → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt PT.isPropPropTrunc PT.isPropPropTrunc
        (replace-left xs xs′ ys ε same)
        (replace-left xs′ xs ys ε (λ δ → match-sym xs xs′ δ (same δ)))))
    (λ xs ys ys′ same → Σ≡Prop (λ _ → isPropIsProp)
      (hPropExt PT.isPropPropTrunc PT.isPropPropTrunc
        (replace-right xs ys ys′ ε same)
        (replace-right xs ys′ ys ε (λ δ → match-sym ys ys′ δ (same δ)))))

infix 4 _near[_]_
_near[_]_ : Configuration → ℚ₊ → Configuration → Type₀
x near[ ε ] y = fst (closeProp ε x y)

near-prop : ∀ x y ε → isProp (x near[ ε ] y)
near-prop x y ε = snd (closeProp ε x y)

opaque
  unfolding closeProp

  insertion-closeness : ∀ xs ys ε → (insert xs near[ ε ] insert ys) ≃ Match xs ε ys
  insertion-closeness xs ys ε = idEquiv (Match xs ε ys)

near-refl : ∀ x ε → x near[ ε ] x
near-refl = SQ.elimProp {P = λ x → ∀ ε → x near[ ε ] x}
  (λ x → isPropΠ (near-prop x x))
  (λ xs ε → invEq (insertion-closeness xs xs ε) (match-refl xs ε))

near-sym : ∀ x y ε → x near[ ε ] y → y near[ ε ] x
near-sym = SQ.elimProp2 {P = λ x y → ∀ ε → x near[ ε ] y → y near[ ε ] x}
  (λ x y → isPropΠ2 λ ε _ → near-prop y x ε)
  (λ xs ys ε close → invEq (insertion-closeness ys xs ε)
    (match-sym xs ys ε (equivFun (insertion-closeness xs ys ε) close)))

near-separated : ∀ x y → (∀ ε → x near[ ε ] y) → x ≡ y
near-separated = SQ.elimProp2 {P = λ x y → (∀ ε → x near[ ε ] y) → x ≡ y}
  (λ x y → isPropΠ λ _ → SQ.squash/ x y)
  (λ xs ys same → SQ.eq/ xs ys (λ ε → equivFun (insertion-closeness xs ys ε) (same ε)))

near-triangle : ∀ x y z ε δ → x near[ ε ] y → y near[ δ ] z → x near[ ε +₊ δ ] z
near-triangle x y z ε δ = SQ.elimProp3
  {P = λ a b c → a near[ ε ] b → b near[ δ ] c → a near[ ε +₊ δ ] c}
  (λ a b c → isPropΠ2 λ _ _ → near-prop a c (ε +₊ δ))
  (λ xs ys zs xy yz → invEq (insertion-closeness xs zs (ε +₊ δ))
    (match-triangle xs ys zs ε δ
      (equivFun (insertion-closeness xs ys ε) xy)
      (equivFun (insertion-closeness ys zs δ) yz))) x y z

near-rounded : ∀ x y ε → x near[ ε ] y →
  PT.∥ Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x near[ δ ] y) ∥₁
near-rounded = SQ.elimProp2
  {P = λ x y → ∀ ε → x near[ ε ] y → PT.∥ Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x near[ δ ] y) ∥₁}
  (λ x y → isPropΠ2 λ _ _ → PT.isPropPropTrunc)
  (λ xs ys ε close → PT.map
    (λ { (δ , below , smaller) → δ , below , invEq (insertion-closeness xs ys δ) smaller })
    (match-rounded xs ys ε (equivFun (insertion-closeness xs ys ε) close)))

configurationSpace : PremetricSpace ℓ-zero ℓ-zero
fst configurationSpace = Configuration
PremetricStr._≈[_]_ (snd configurationSpace) = _near[_]_
PremetricStr.isPremetric (snd configurationSpace) .IsPremetric.isSetM = SQ.squash/
PremetricStr.isPremetric (snd configurationSpace) .IsPremetric.isProp≈ = near-prop
PremetricStr.isPremetric (snd configurationSpace) .IsPremetric.isRefl≈ = near-refl
PremetricStr.isPremetric (snd configurationSpace) .IsPremetric.isSym≈ = near-sym
PremetricStr.isPremetric (snd configurationSpace) .IsPremetric.isSeparated≈ = near-separated
PremetricStr.isPremetric (snd configurationSpace) .IsPremetric.isTriangular≈ = near-triangle
PremetricStr.isPremetric (snd configurationSpace) .IsPremetric.isRounded≈ = near-rounded
