module Cubical.HITs.CauchyReals.Circle.Homotopy.Invariance where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Int.Fast as ℤ using (ℤ; isSetℤ)
open import Cubical.Data.Rationals as ℚ using (ℚ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
import Cubical.Data.Rationals.Inverse as ℚ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals using
  (ℚ₊; min₊; min₊≤L; min₊≤R; [_/_]₊)
import Cubical.HITs.CauchyReals.Foundation.Rationals as QR
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Ring using (module Rℝ)
open import Cubical.HITs.CauchyReals.Trigonometry.Identities using (injFromNatℚ)
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.HITs.CauchyReals.Circle.Winding.Angle
open import Cubical.HITs.CauchyReals.Circle.Winding.Subdivision
open import Cubical.HITs.CauchyReals.Circle.Winding.Continuity
open import Cubical.HITs.CauchyReals.Circle.Winding.Loop
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals
open import Cubical.Tactics.CommRingSolver.OrderedReflection

private
  module C = PremetricStr (snd distCirclePremetricSpace)

opaque
  comparison-radius : ℚ₊
  comparison-radius = [ 1 / 2 ]₊

-- A rectangular grid compares the short increments on its bottom and top.
module Bridge (f g : ℚ → distCircle) (vertical : ∀ x → Near (f x) (g x)) where
  private
    module F = Subdivision f
    module G = Subdivision g

  CrossSmall : ℚ → ℚ → Type
  CrossSmall a b = ∀ x y → a ℚ.≤ x → x ℚ.≤ b →
    a ℚ.≤ y → y ℚ.≤ b → Near (f x) (g y)

  CrossFine : ℕ → ℚ → ℚ → Type
  CrossFine zero a b = CrossSmall a b
  CrossFine (suc n) a b = CrossFine n a (mid a b) × CrossFine n (mid a b) b

  cross-from-mesh : ∀ n a b → a ℚ.≤ b → (δ : ℚ₊) →
    (∀ x y → QR.abs (x ℚ.- y) ℚ.< fst δ → Near (f x) (g y)) →
    mesh n a b ℚ.< fst δ → CrossFine n a b
  cross-from-mesh zero a b a≤b δ close bound x y a≤x x≤b a≤y y≤b =
    close x y (ℚ.isTrans≤< _ (b ℚ.- a) _
      (ℚ.absFrom≤×≤ (b ℚ.- a) (x ℚ.- y)
        <≤ℚ![ a≤x ][ y≤b ] <≤ℚ![ a≤y ][ x≤b ])
      (subst (ℚ._< fst δ) (ℚ.·IdR (b ℚ.- a)) bound))
  cross-from-mesh (suc n) a b a≤b δ close bound =
    cross-from-mesh n a (mid a b) (mid-left a b a≤b) δ close
      (subst (ℚ._< fst δ) (sym (mesh-left n a b)) bound) ,
    cross-from-mesh n (mid a b) b (mid-right a b a≤b) δ close
      (subst (ℚ._< fst δ) (sym (mesh-right n a b)) bound)

  turns-bridge : ∀ n a b a≤b fine fine' → CrossFine n a b →
    F.turns n a b a≤b fine +ᵣ shortAngle (f b) (g b) (vertical b) ≡
    shortAngle (f a) (g a) (vertical a) +ᵣ G.turns n a b a≤b fine'
  turns-bridge zero a b a≤b fine fine' cross =
    shortAngle-add (f a) (f b) (g b) _ _ diagonal
    ∙ sym (shortAngle-add (f a) (g a) (g b) _ _ diagonal)
    where
    diagonal : Near (f a) (g b)
    diagonal = cross a b (ℚ.isRefl≤ a) a≤b a≤b (ℚ.isRefl≤ b)
  turns-bridge (suc n) a b a≤b fine fine' cross =
    sym (+ᵣAssoc _ _ _)
    ∙ cong (F.turns n a (mid a b) (mid-left a b a≤b) (fst fine) +ᵣ_)
        (turns-bridge n (mid a b) b (mid-right a b a≤b)
          (snd fine) (snd fine') (snd cross))
    ∙ +ᵣAssoc _ _ _
    ∙ cong (_+ᵣ G.turns n (mid a b) b (mid-right a b a≤b) (snd fine'))
        (turns-bridge n a (mid a b) (mid-left a b a≤b)
          (fst fine) (fst fine') (fst cross))
    ∙ sym (+ᵣAssoc _ _ _)

  closed-turns : (f-loop : f 0 ≡ f 1) (g-loop : g 0 ≡ g 1) →
    ∀ n fine fine' → CrossFine n 0 1 →
    F.turns n 0 1 unit-order fine ≡ G.turns n 0 1 unit-order fine'
  closed-turns f-loop g-loop n fine fine' cross =
    sym (Rℝ.plusMinus (F.turns n 0 1 unit-order fine) _)
    ∙ cong (_-ᵣ shortAngle (f 1) (g 1) (vertical 1))
      (turns-bridge n 0 1 unit-order fine fine' cross
        ∙ cong (_+ᵣ G.turns n 0 1 unit-order fine') endpoint
        ∙ +ᵣComm _ _)
    ∙ Rℝ.plusMinus (G.turns n 0 1 unit-order fine') _
    where
    endpoint : shortAngle (f 0) (g 0) (vertical 0) ≡
      shortAngle (f 1) (g 1) (vertical 1)
    endpoint = cong (λ (p : Σ[ x ∈ distCircle ] Σ[ y ∈ distCircle ] Near x y) →
      shortAngle (fst p) (fst (snd p)) (snd (snd p)))
      (ΣPathP (f-loop , ΣPathP (g-loop , isProp→PathP (λ i →
        isProp<ᵣ _ _) _ _)))

private
  opaque
    unfolding comparison-radius
    half-near : ∀ p q → p C.≈[ comparison-radius ] q → Near p q
    half-near p q close = metric-close→Near p q
      (C.isMonotone≈< p q (comparison-radius) 1 <≤ℚ! close)

    cross-near : ∀ p q r → p C.≈[ comparison-radius ] q →
      q C.≈[ comparison-radius ] r → Near p r
    cross-near p q r pq qr = metric-close→Near p r
      (C.subst≈ p r {ε = (comparison-radius) QR.+₊ (comparison-radius)} {ε' = 1}
        ℚ! (C.isTriangular≈ p q r (comparison-radius) (comparison-radius) pq qr))

-- Uniformly close loops have the same winding number. The comparison
-- uses only a finite grid and local angular identities.
windingLoop-close :
  (f g : UC[ ℝPremetricSpace , distCirclePremetricSpace ]) →
  (fl : fst f 0 ≡ fst f 1) (gl : fst g 0 ≡ fst g 1) →
  (∀ x → fst f x C.≈[ comparison-radius ] fst g x) →
  windingLoop f fl ≡ windingLoop g gl
windingLoop-close f g fl gl close = PT.rec2 (isSetℤ _ _) compare (snd f) (snd g)
  where
  module F = Subdivision (fst f ∘ rat)
  module G = Subdivision (fst g ∘ rat)
  module B = Bridge (fst f ∘ rat) (fst g ∘ rat)
    (λ x → half-near (fst f (rat x)) (fst g (rat x)) (close (rat x)))

  compare :
    (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith
      (snd ℝPremetricSpace) (fst f) (snd distCirclePremetricSpace) μ) →
    (Σ[ ν ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith
      (snd ℝPremetricSpace) (fst g) (snd distCirclePremetricSpace) ν) →
    windingLoop f fl ≡ windingLoop g gl
  compare (μ , fc) (ν , gc) = injFromNatℚ _ _ (inj-rat _ _
    (sym (windingLoop-subdivision f fl n finef)
      ∙ B.closed-turns fl gl n finef fineg cross
      ∙ windingLoop-subdivision g gl n fineg))
    where
    δ : ℚ₊
    δ = min₊ (μ (comparison-radius)) (ν (comparison-radius))
    n : ℕ
    n = fst (ℚ.1/2ⁿ<ε δ)
    bound : mesh n 0 1 ℚ.< fst δ
    bound = subst (ℚ._< fst δ) (sym (ℚ.·IdL _)) (snd (ℚ.1/2ⁿ<ε δ))

    f-close : ∀ x y → QR.abs (x ℚ.- y) ℚ.< fst δ →
      fst f (rat x) C.≈[ comparison-radius ] fst f (rat y)
    f-close x y xy = IsUniformlyContinuousWith.pres≈ fc (rat x) (rat y) (comparison-radius)
      (∼→≈ℝ (rat x) (rat y) (μ (comparison-radius)) (rat-rat-fromAbs x y (μ (comparison-radius))
        (ℚ.isTrans<≤ _ _ _ xy (min₊≤L (μ (comparison-radius)) (ν (comparison-radius))))))

    g-close : ∀ x y → QR.abs (x ℚ.- y) ℚ.< fst δ →
      fst g (rat x) C.≈[ comparison-radius ] fst g (rat y)
    g-close x y xy = IsUniformlyContinuousWith.pres≈ gc (rat x) (rat y) (comparison-radius)
      (∼→≈ℝ (rat x) (rat y) (ν (comparison-radius)) (rat-rat-fromAbs x y (ν (comparison-radius))
        (ℚ.isTrans<≤ _ _ _ xy (min₊≤R (μ (comparison-radius)) (ν (comparison-radius))))))

    finef : F.Fine n 0 1
    finef = F.fine-from-mesh n 0 1 unit-order δ
      (λ x y xy → half-near (fst f (rat x)) (fst f (rat y)) (f-close x y xy)) bound
    fineg : G.Fine n 0 1
    fineg = G.fine-from-mesh n 0 1 unit-order δ
      (λ x y xy → half-near (fst g (rat x)) (fst g (rat y)) (g-close x y xy)) bound
    cross : B.CrossFine n 0 1
    cross = B.cross-from-mesh n 0 1 unit-order δ
      (λ x y xy → cross-near (fst f (rat x)) (fst f (rat y)) (fst g (rat y))
        (f-close x y xy) (close (rat y))) bound
