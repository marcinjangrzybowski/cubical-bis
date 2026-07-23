module Cubical.HITs.CauchyReals.ArcSin.Symmetric.Properties.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport using (substEquiv)

open import Cubical.Data.Int as ℤ using (pos)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals as ℚ using (ℚ ; [_/_])
open import Cubical.Data.Rationals.Order as ℚ using (_≤_ ; clamp)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ using (≤cases)
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.PropositionalTruncation.Properties using (propTruncIdempotent≃)

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ₊)
open import Cubical.HITs.CauchyReals.Foundation.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base hiding
  (sym-intervalℙ⊆ointervalℙ)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Predicate using
  (sym-intervalℙ⊆ointervalℙ)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Clamp using
  (clampᵣ∈intervalℙ)
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Calculus.Integration.Partition.Base using (ℚ<→0<)
open import Cubical.HITs.CauchyReals.Foundation.Order.Positive
open import Cubical.HITs.CauchyReals.Trigonometry.Base
open import Cubical.HITs.CauchyReals.Trigonometry.Pi

open import Cubical.HITs.CauchyReals.ArcSin.Symmetric.Properties.Rational public
open import Cubical.HITs.CauchyReals.ArcSin.Symmetric.Properties.Continuity public

opaque
  arcSin⟨⟩∘sin : ∀ x sinx∈
   → x ∈ ointervalℙ (-ᵣ π-number/2) π-number/2
   → arcSin⟨⟩ (sin x) sinx∈ ≡ x
  arcSin⟨⟩∘sin x sinx∈@(<negx , x<) x∈ =
    PT.rec (isSetℝ _ _)
      (λ (Q , ∣x∣<Q , Q<π/2) →
        let Q₊ = (Q , (ℚ<→0< Q (<ᵣ→<ℚ _ _ (isTrans≤<ᵣ _ _ _ (0≤absᵣ _) ∣x∣<Q))))
            x∈Q : x ∈ intervalℙ (rat (ℚ.- Q)) (rat Q)
            x∈Q = isTrans≤≡ᵣ _ _ _ (isTrans≡≤ᵣ _ _ _ (sym (-ᵣ-rat Q))
                   (-ᵣ≤ᵣ _ _
                    (isTrans≤ᵣ _ _ _ (≤absᵣ _)
                      (isTrans≡≤ᵣ _ _ _ (sym (-absᵣ _)) (<ᵣWeaken≤ᵣ _ _ ∣x∣<Q) ))))
                      (-ᵣInvol _ ) ,
                   isTrans≤ᵣ _ _ _ (≤absᵣ _)
                   (<ᵣWeaken≤ᵣ _ _ ∣x∣<Q )

            zzz = cong (uncurry arcSin⟨⟩)
                  (Σ≡Prop (∈-isProp (ointervalℙ (-1) 1))
                    {u = _ , (<negx , x<)}
                    {v = _ , _}
                        (cong sin
                         ((∈ℚintervalℙ→clampᵣ≡ (rat ((ℚ.- Q))) (rat Q)
                   x x∈Q))))

        in zzz ∙∙
           ≡Continuous
             (λ x → arcSin⟨⟩ (sin (clampᵣ (rat (ℚ.- Q)) (rat Q) x))
                       (⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ _ (sym-intervalℙ⊆ointervalℙ _ _ Q<π/2
                        _ (
                          subst (λ -Q → clampᵣ (rat (ℚ.- Q)) (rat Q) x ∈
                            intervalℙ -Q (rat Q))
                            (sym (-ᵣ-rat Q))
                             ((clampᵣ∈intervalℙ (rat (ℚ.- Q)) (rat Q)
                               (isTrans≡≤ᵣ _ _ _
                                 (sym (-ᵣ-rat Q))
                                 (<ᵣWeaken≤ᵣ _ _ (-ℝ₊<ℝ₊ (ℚ₊→ℝ₊ Q₊) (ℚ₊→ℝ₊ Q₊)))) x))))))
             (λ x → clampᵣ (rat ((ℚ.- Q))) (rat Q) x)
             (IsContinuousWithPred∘IsContinuous
                (ointervalℙ -1 1)
                 arcSin⟨⟩ _ _
                 IsContinuousWPArcSin⟨⟩
                  (IsContinuous∘ _ _
                    (isContinuousSin)
                    (IsContinuousClamp (rat ((ℚ.- Q))) (rat Q))))
             (IsContinuousClamp (rat ((ℚ.- Q))) (rat Q))

             (λ q →
              let z = sym (clampᵣ-rat (ℚ.- Q) Q q)
                  q∈ = (subst-∈ (intervalℙ (-ᵣ rat Q) (rat Q))
                       ((cong clampᵣ (-ᵣ-rat Q) ≡$ rat Q ≡$ rat q) ∙ sym z)
                       (clampᵣ∈intervalℙ _ (rat Q)
                         (<ᵣWeaken≤ᵣ _ _ (-ℝ₊<ℝ₊ (ℚ₊→ℝ₊ Q₊) (ℚ₊→ℝ₊ Q₊))) (rat q)))
                  sinq∈ : sin (rat (ℚ.clamp (ℚ.- Q) Q q)) ∈ ointervalℙ -1 1
                  sinq∈ = ⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ _
                    (sym-intervalℙ⊆ointervalℙ (rat Q) π-number/2
                      Q<π/2 (rat (ℚ.clamp (ℚ.- Q) Q q)) q∈)
              in cong (uncurry arcSin⟨⟩)
                  (Σ≡Prop (∈-isProp (ointervalℙ (-1) 1))
                        (cong sin (sym z)))
                    ∙∙ arcSin⟨⟩∘sin-ℚ Q₊ Q<π/2
                     (ℚ.clamp (ℚ.- Q) Q q)
                      (ℚ.≤cases 0 (ℚ.clamp (ℚ.- Q) Q q)) q∈ sinq∈ ∙∙ z)
                 x
           ∙∙ (sym (∈ℚintervalℙ→clampᵣ≡ (rat ((ℚ.- Q))) (rat Q)
                   x x∈Q)))
      (denseℚinℝ (absᵣ x) π-number/2  (
       ointerval→abs< x π-number/2 x∈))


  sin∘arcSin⟨⟩ : ∀ x x∈ → sin (arcSin⟨⟩ x x∈) ≡ x
  sin∘arcSin⟨⟩ x x∈ = fst (propTruncIdempotent≃ (isSetℝ _ _)) $ do
    let h = λ (x : ℝ) → substEquiv (λ X → x ∈
            ointervalℙ X (rat [ pos 1 / 1+ 0 ]))
           (sym (-ᵣ-rat 1))
    (q , ∣x∣<q , q<1) ← denseℚinℝ (absᵣ x) 1 (ointerval→abs< x 1
          (fst (h x) x∈))
    let q₊ : ℚ₊
        q₊ = q , ℚ<→0< q (<ᵣ→<ℚ _ _ (isTrans≤<ᵣ _ _ _ (0≤absᵣ _) ∣x∣<q))
        p = ∈ℚintervalℙ→clampᵣ≡ (-ᵣ (rat q)) (rat q) x
              (abs≤→interval x (rat q) (<ᵣWeaken≤ᵣ _ _ ∣x∣<q))
        hh = clampᵣ∈intervalℙ _ _
                  (<ᵣWeaken≤ᵣ _ _ (-ℝ₊<ℝ₊ (ℚ₊→ℝ₊ q₊) (ℚ₊→ℝ₊ q₊)))
    ∣ cong sin (cong (uncurry arcSin⟨⟩)
         (Σ≡Prop (∈-isProp (ointervalℙ _ _))
           p))
      ∙∙ ≡Continuous
          (λ x → sin (arcSin⟨⟩
            (clampᵣ (-ᵣ (rat q)) (rat q) x)
              (invEq (h _) (sym-intervalℙ⊆ointervalℙ (rat q) 1 q<1  _
                 (hh x)))))
          (clampᵣ (-ᵣ (rat q)) (rat q))
          (IsContinuous∘ _ _ isContinuousSin
             (IsContinuousWithPred∘IsContinuous
               (ointervalℙ -1 1)
               _
               _
               (λ x → invEq (h _)
                  (sym-intervalℙ⊆ointervalℙ (rat q) 1 q<1  _ _))
               IsContinuousWPArcSin⟨⟩
               (IsContinuousClamp (-ᵣ (rat q)) (rat q))))
          (IsContinuousClamp (-ᵣ (rat q)) (rat q))
           (λ y →
           let p' = sym (sym-clamp-rat y q₊)
           in cong sin (cong (uncurry arcSin⟨⟩)
                (Σ≡Prop (∈-isProp (ointervalℙ -1 1))
                  (sym p'))) ∙
               sin∘arcSin⟨⟩ℚ
               (ℚ.clamp (ℚ.- q) q y)
               (invEq (h _) (sym-intervalℙ⊆ointervalℙ (rat q) 1 q<1  _
                    ((subst-∈ (intervalℙ (-ᵣ rat q) (rat q))
                       (sym-clamp-rat y q₊)
                      (hh (rat y)) ))))
                (ℚ.≤cases 0 (ℚ.clamp (ℚ.- q) q y))
                   ∙ p')
           x
      ∙∙ sym p ∣₁


sinIso⟨-π/2,π2⟩ : Iso (Σ _ (_∈ ointervalℙ (-ᵣ π-number/2) π-number/2))
                      (Σ _ (_∈ ointervalℙ -1 1))
sinIso⟨-π/2,π2⟩ .Iso.fun (x , x∈) = sin x , ⟨-π/2,π/2⟩→sin∈⟨-1,1⟩ x x∈
sinIso⟨-π/2,π2⟩ .Iso.inv (x , x∈) = arcSin⟨⟩ x x∈ , arcSin⟨⟩∈ x x∈
sinIso⟨-π/2,π2⟩ .Iso.sec (x , x∈) =
  Σ≡Prop (∈-isProp (ointervalℙ -1 1))
    (sin∘arcSin⟨⟩ _ _)
sinIso⟨-π/2,π2⟩ .Iso.ret (x , x∈) =
  Σ≡Prop (∈-isProp (ointervalℙ (-ᵣ π-number/2) π-number/2))
    (arcSin⟨⟩∘sin _ _ x∈)


equivSin⟨⟩ : (Σ _ (_∈ ointervalℙ (-ᵣ π-number/2) π-number/2))
             ≃ (Σ _ (_∈ ointervalℙ -1 1))
equivSin⟨⟩ = isoToEquiv sinIso⟨-π/2,π2⟩
