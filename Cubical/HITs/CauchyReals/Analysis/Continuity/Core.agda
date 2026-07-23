module Cubical.HITs.CauchyReals.Analysis.Continuity.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.Tactics.CauchyReals.ExpressionLifting


IsContinuous : (ℝ → ℝ) → Type
IsContinuous f =
 ∀ u ε → ∃[ δ ∈ ℚ₊ ] (∀ v → u ∼[ δ ] v → f u ∼[ ε ] f v)


isPropIsContinuous : ∀ f → isProp (IsContinuous f)
isPropIsContinuous f = isPropΠ2 λ _ _ → squash₁


Lipschitz→IsContinuous : ∀ L f → Lipschitz-ℝ→ℝ L f → IsContinuous f
Lipschitz→IsContinuous L f p u ε =
 ∣ (L ℚ.⁻¹₊) ·₊ ε ,
   (λ v → subst∼ ℚ!
      ∘S p u v ((L ℚ.⁻¹₊) ·₊ ε)) ∣₁


IsContinuous∘ : ∀ f g → IsContinuous f → IsContinuous g
                    → IsContinuous (f ∘ g)
IsContinuous∘ f g fC gC u ε =
  PT.rec squash₁
    (λ (δ , δ∼) →
      PT.map (map-snd λ x v → δ∼ (g v) ∘ (x _)) (gC u δ))
    (fC (g u) ε)


-- HoTT Lemma 11.3.39
≡Continuous : ∀ f g → IsContinuous f → IsContinuous g
                → (∀ r → f (rat r) ≡ g (rat r))
                → ∀ u → f u ≡ g u
≡Continuous f g fC gC p = Elimℝ-Prop.go w
 where
 w : Elimℝ-Prop (λ z → f z ≡ g z)
 w .Elimℝ-Prop.ratA = p
 w .Elimℝ-Prop.limA x xC R = eqℝ _ _ λ ε →
   let f' = fC (lim x xC) (ε /2₊)
       g' = gC (lim x xC) (ε /2₊)
   in PT.rec2
       (isProp∼ _ _ _)
       (λ (θ , θ∼) (η , η∼) →
         let δ = (min₊ θ η) /2₊

             zF : f (lim x xC) ∼[ ε /2₊ ] g (x δ)
             zF = subst (f (lim x xC) ∼[ ε /2₊ ]_)
                  (R _)
                  (θ∼ _ (∼-monotone≤
                    (subst (ℚ._≤ fst θ)
                      ℚ!!
                      (ℚ.min≤ (fst θ) (fst η)))
                    (sym∼ _ _ _ (𝕣-lim-self x xC δ δ))))

             zG : g (lim x xC) ∼[ ε /2₊ ] g (x δ)
             zG = η∼ _ (∼-monotone≤
                    (subst (ℚ._≤ fst η)
                      ℚ!!
                      (ℚ.min≤' (fst θ) (fst η)))
                    (sym∼ _ _ _ (𝕣-lim-self x xC δ δ)))
         in subst∼ ℚ!! (triangle∼ zF (sym∼ _ _ _ zG)))
       f' g'
 w .Elimℝ-Prop.isPropA _ = isSetℝ _ _


IsContinuousId : IsContinuous (λ x → x)
IsContinuousId u ε = ∣ ε , (λ _ x → x) ∣₁


IsContinuousConst : ∀ x → IsContinuous (λ _ → x)
IsContinuousConst x u ε = ∣ ε , (λ _ _ → refl∼ _ _) ∣₁


opaque
 unfolding absᵣ _<ᵣ_

 IsContinuousAbsᵣ : IsContinuous absᵣ
 IsContinuousAbsᵣ = Lipschitz→IsContinuous 1 _ absᵣ-lip


IsContinuous-ᵣ : IsContinuous (-ᵣ_)
IsContinuous-ᵣ = Lipschitz→IsContinuous 1 _ -ᵣ-lip


opaque
 unfolding maxᵣ minᵣ

 IsContinuousMaxR : ∀ x → IsContinuous (λ u → maxᵣ u x)
 IsContinuousMaxR x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼L maxR _ _ _ ε) ∣₁

 IsContinuousMaxL : ∀ x → IsContinuous (maxᵣ x)
 IsContinuousMaxL x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼R maxR x _ _ ε) ∣₁

 IsContinuousMinR : ∀ x → IsContinuous (λ u → minᵣ u x)
 IsContinuousMinR x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼L minR _ _ _ ε) ∣₁

 IsContinuousMinL : ∀ x → IsContinuous (minᵣ x)
 IsContinuousMinL x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼R minR x _ _ ε) ∣₁


opaque
 unfolding _+ᵣ_

 IsContinuous+ᵣR : ∀ x → IsContinuous (_+ᵣ x)
 IsContinuous+ᵣR x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼L sumR _ _ _ ε) ∣₁

 IsContinuous+ᵣL : ∀ x → IsContinuous (x +ᵣ_)
 IsContinuous+ᵣL x u ε =
  ∣ ε , (λ v → NonExpanding₂.go∼R sumR x _ _ ε) ∣₁


contDiagNE₂ : ∀ {h} → (ne : NonExpanding₂ h)
  → ∀ f g → IsContinuous f → IsContinuous g
  → IsContinuous (λ x → NonExpanding₂.go ne (f x) (g x))
contDiagNE₂ ne f g fC gC u ε =
  PT.map2
    (λ (x , x') (y , y') →
      min₊ x y , λ v z →
        subst∼ ℚ!!
          (NonExpanding₂.go∼₂ ne (ε /2₊) (ε /2₊)
            (x' v (∼-monotone≤ (ℚ.min≤ (fst x) (fst y)) z))
            (y' v (∼-monotone≤ (ℚ.min≤' (fst x) (fst y)) z))))
    (fC u (ε /2₊)) (gC u (ε /2₊))


opaque
 unfolding maxᵣ

 cont₂maxᵣ : ∀ f g → IsContinuous f → IsContinuous g
   → IsContinuous (λ x → maxᵣ (f x) (g x))
 cont₂maxᵣ = contDiagNE₂ maxR


opaque
 unfolding minᵣ

 cont₂minᵣ : ∀ f g → IsContinuous f → IsContinuous g
   → IsContinuous (λ x → minᵣ (f x) (g x))
 cont₂minᵣ = contDiagNE₂ minR


IsContinuous₂ : (ℝ → ℝ → ℝ) → Type
IsContinuous₂ f =
  (∀ x → IsContinuous (f x)) × (∀ x → IsContinuous (flip f x))


IsContinuous₂Const : ∀ x → IsContinuous₂ (λ _ _ → x)
IsContinuous₂Const x =
  (λ _ → IsContinuousConst _) , (λ _ → IsContinuousConst _)


cont₂-fst : IsContinuous₂ (λ x _ → x)
cont₂-fst = (λ _ → IsContinuousConst _) , (λ _ → IsContinuousId)


cont₂-snd : IsContinuous₂ (λ _ x → x)
cont₂-snd = (λ _ → IsContinuousId) , (λ _ → IsContinuousConst _)


cont₂-id : ∀ x → IsContinuous₂ (λ _ _ → x)
cont₂-id _ = (λ _ → IsContinuousConst _) , (λ _ → IsContinuousConst _)


asIsContinuous₂-fst : ∀ f → IsContinuous f → IsContinuous₂ (λ x _ → f x)
asIsContinuous₂-fst f cf = (λ _ → IsContinuousConst _) , λ _ → cf


asIsContinuous₂-snd : ∀ f → IsContinuous f → IsContinuous₂ (λ _ x → f x)
asIsContinuous₂-snd f cf = (λ _ → cf) , (λ _ → IsContinuousConst _)


≡Cont₂ : {f₀ f₁ : ℝ → ℝ → ℝ}
       → IsContinuous₂ f₀
       → IsContinuous₂ f₁
       → (∀ u u' → f₀ (rat u) (rat u') ≡ f₁ (rat u) (rat u'))
       → ∀ x x' → f₀ x x' ≡ f₁ x x'
≡Cont₂ {f₀} {f₁} (f₀C , f₀C') (f₁C , f₁C') p x =
  ≡Continuous _ _ (f₀C x) (f₁C x)
    (λ q → ≡Continuous _ _ (f₀C' (rat q)) (f₁C' (rat q))
       (λ r → p r q) x)


contNE₂∘ : ∀ {h} → (ne : NonExpanding₂ h)
  {f₀ f₁ : ℝ → ℝ → ℝ}
  → IsContinuous₂ f₀
  → IsContinuous₂ f₁
  → IsContinuous₂
      (λ x x' → NonExpanding₂.go ne (f₀ x x') (f₁ x x'))
contNE₂∘ ne f₀C f₁C =
  (λ x → contDiagNE₂ ne _ _ (f₀C .fst x) (f₁C .fst x)) ,
  λ x → contDiagNE₂ ne _ _ (f₀C .snd x) (f₁C .snd x)


cont∘₂ : ∀ {g} {f : ℝ → ℝ → ℝ}
  → IsContinuous g
  → IsContinuous₂ f
  → IsContinuous₂ (λ x x' → g (f x x'))
cont∘₂ gC (fC , _) .fst x = IsContinuous∘ _ _ gC (fC x)
cont∘₂ gC (_ , fC) .snd x = IsContinuous∘ _ _ gC (fC x)


cont₂∘ : {g : ℝ → ℝ → ℝ} → ∀ {f f'}
  → IsContinuous₂ g
  → IsContinuous f
  → IsContinuous f'
  → IsContinuous₂ (λ x x' → g (f x) (f' x'))
cont₂∘ (gC , _) _ f'C .fst x = IsContinuous∘ _ _ (gC _) f'C
cont₂∘ (_ , gC) fC _ .snd x = IsContinuous∘ _ _ (gC _) fC


contNE₂ : ∀ {h} → (ne : NonExpanding₂ h)
  → IsContinuous₂ (NonExpanding₂.go ne)
contNE₂ ne =
  contNE₂∘ ne
    ((λ _ → IsContinuousConst _) , (λ _ → IsContinuousId))
    ((λ _ → IsContinuousId) , (λ _ → IsContinuousConst _))


opaque
 unfolding _+ᵣ_

 cont₂+ᵣ : ∀ f g → IsContinuous f → IsContinuous g
   → IsContinuous (λ x → f x +ᵣ g x)
 cont₂+ᵣ = contDiagNE₂ sumR


 IsContinuous+₂∘ : ∀ {f₀} {f₁} → IsContinuous₂ f₀ → IsContinuous₂ f₁
   → IsContinuous₂ (λ a b → f₀ a b +ᵣ f₁ a b)
 IsContinuous+₂∘ = contNE₂∘ sumR


 IsContinuous-₂∘ : ∀ {f₀} {f₁} → IsContinuous₂ f₀ → IsContinuous₂ f₁
   → IsContinuous₂ (λ a b → f₀ a b -ᵣ f₁ a b)
 IsContinuous-₂∘ f₀C f₁C =
  contNE₂∘ sumR f₀C (cont∘₂ IsContinuous-ᵣ f₁C)


 IsContinuous-₂ : IsContinuous₂ _-ᵣ_
 IsContinuous-₂ =
  contNE₂∘ sumR (IsContinuousConst , (λ _ → IsContinuousId))
    ((λ _ → IsContinuous-ᵣ) , IsContinuousConst ∘ -ᵣ_)
