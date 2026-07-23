module Cubical.HITs.CauchyReals.Analysis.Continuity.Predicate where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core
open import Cubical.Tactics.CauchyReals.ExpressionLifting
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Strict


IsContinuousWithPred : (P : ℝ → hProp ℓ-zero) →
  (∀ r → ⟨ P r ⟩ → ℝ) → Type
IsContinuousWithPred P f =
  ∀ u ε u∈P →
    ∃[ δ ∈ ℚ₊ ] (∀ v v∈P → u ∼[ δ ] v → f u u∈P ∼[ ε ] f v v∈P)


AsContinuousWithPred : (P : ℝ → hProp ℓ-zero) → (f : ℝ → ℝ)
  → IsContinuous f
  → IsContinuousWithPred P (λ x _ → f x)
AsContinuousWithPred P f fC u ε _ =
  PT.map (map-snd (λ δ∼ v _ → δ∼ v)) (fC u ε)


IsContinuousWP∘ : ∀ P P' f g → (h : ∀ r x → ⟨ P (g r x) ⟩)
  → IsContinuousWithPred P f
  → IsContinuousWithPred P' g
  → IsContinuousWithPred P' (λ r x → f (g r x) (h r x))
IsContinuousWP∘ P P' f g h fC gC u ε u∈P =
  PT.rec squash₁
    (λ (δ , δ∼) →
      PT.map (map-snd λ η∼ v v∈P →
        δ∼ (g v v∈P) (h v v∈P) ∘ η∼ v v∈P)
        (gC u δ u∈P))
    (fC (g u u∈P) ε (h _ u∈P))


openPred : (P : ℝ → hProp ℓ-zero) → hProp ℓ-zero
openPred P =
  (∀ x → ⟨ P x ⟩ → ∃[ δ ∈ ℚ₊ ] (∀ y → x ∼[ δ ] y → ⟨ P y ⟩)) ,
  isPropΠ2 λ _ _ → squash₁


contDiagNE₂WP : ∀ {h} → (ne : NonExpanding₂ h)
  → ∀ P f g
  → IsContinuousWithPred P f
  → IsContinuousWithPred P g
  → IsContinuousWithPred P
      (λ x x∈ → NonExpanding₂.go ne (f x x∈) (g x x∈))
contDiagNE₂WP ne P f g fC gC u ε u∈ =
  PT.map2
    (λ (δ , δ∼) (η , η∼) →
      min₊ δ η , λ v v∈ u∼v →
        subst∼ ℚ!!
          (NonExpanding₂.go∼₂ ne (ε /2₊) (ε /2₊)
            (δ∼ v v∈
              (∼-monotone≤ (ℚ.min≤ (fst δ) (fst η)) u∼v))
            (η∼ v v∈
              (∼-monotone≤ (ℚ.min≤' (fst δ) (fst η)) u∼v))))
    (fC u (ε /2₊) u∈) (gC u (ε /2₊) u∈)


opaque

 IsContinuousWithPred∘IsContinuous : ∀ P f g
   → (g∈ : ∀ x → g x ∈ P)
   → IsContinuousWithPred P f
   → IsContinuous g
   → IsContinuous λ x → f (g x) (g∈ x)
 IsContinuousWithPred∘IsContinuous P f g g∈ fC gC u ε =
   PT.rec squash₁
     (λ (δ , δ∼) →
       PT.map (map-snd λ η∼ v u∼v →
         δ∼ (g v) (g∈ v) (η∼ v u∼v))
         (gC u δ))
     (fC (g u) ε (g∈ u))


 IsContinuousWP∘' : ∀ P f g
   → IsContinuous f
   → IsContinuousWithPred P g
   → IsContinuousWithPred P (λ r x → f (g r x))
 IsContinuousWP∘' P f g fC gC u ε u∈P =
   PT.rec squash₁
     (λ (δ , δ∼) →
       PT.map (map-snd λ η∼ v v∈P →
         δ∼ (g v v∈P) ∘ η∼ v v∈P)
         (gC u δ u∈P))
     (fC (g u u∈P) ε)


 IsContinuousWithPred-ᵣ : ∀ P f → IsContinuousWithPred P f →
   IsContinuousWithPred P λ x x∈ → -ᵣ (f x x∈)
 IsContinuousWithPred-ᵣ P f =
   IsContinuousWP∘' P _ _ IsContinuous-ᵣ


 contDropPred : ∀ f → IsContinuousWithPred ⊤Pred (λ x _ → f x)
   → IsContinuous f
 contDropPred f =
   flip (IsContinuousWithPred∘IsContinuous ⊤Pred (λ x _ → f x)
     (idfun _) _) IsContinuousId


 ∩-openPred : ∀ P Q → ⟨ openPred P ⟩ → ⟨ openPred Q ⟩ →
   ⟨ openPred (λ x → _ , isProp× (snd (P x)) (snd (Q x))) ⟩
 ∩-openPred _ _ oP oQ x (x∈P , x∈Q) =
   PT.map2
     (λ (δ , Pδ) (η , Qη) →
       min₊ δ η , λ y x∼y →
         Pδ y (∼-monotone≤ (ℚ.min≤ _ _) x∼y) ,
         Qη y (∼-monotone≤ (ℚ.min≤' (fst δ) (fst η)) x∼y))
     (oP x x∈P) (oQ x x∈Q)


lowerℚBound : ∀ u → 0 <ᵣ u → ∃[ ε ∈ ℚ₊ ] (rat (fst ε) <ᵣ u)
lowerℚBound u =
  PT.map (λ (ε , (x' , x'')) → (ε , <ᵣ→<ℚ _ _ x') , x'')
  ∘ denseℚinℝ 0 u


openPred< : ∀ x → ⟨ openPred (λ y → (x <ᵣ y) , isProp<ᵣ _ _) ⟩
openPred< x y =
  PT.map (map-snd (λ {q} a<y-x v →
      isTrans<ᵣ _ _ _ (a<b-c⇒c<b-a-bootstrap (rat (fst q)) y x a<y-x)
      ∘S a-b<c⇒a-c<b-bootstrap y v (rat (fst q))
      ∘S isTrans≤<ᵣ _ _ _ (≤absᵣ _)
      ∘S fst (∼≃abs<ε _ _ _)))
  ∘S lowerℚBound (y +ᵣ (-ᵣ x))
  ∘S x<y→0<y-x-bootstrap x y


openPred> : ∀ x → ⟨ openPred (λ y → (y <ᵣ x) , isProp<ᵣ _ _) ⟩
openPred> x y =
  PT.map (map-snd (λ {q} q<x-y v →
      flip (isTrans<ᵣ _ _ _)
        (a<b-c⇒a+c<b-bootstrap (rat (fst q)) x y q<x-y)
      ∘S a-b<c⇒a<c+b-bootstrap v y (rat (fst q))
      ∘S isTrans≤<ᵣ _ _ _ (≤absᵣ _)
      ∘S fst (∼≃abs<ε _ _ _)
      ∘S sym∼ _ _ _))
  ∘S lowerℚBound (x +ᵣ (-ᵣ y))
  ∘S x<y→0<y-x-bootstrap y x


openIintervalℙ : ∀ a b → ⟨ openPred (ointervalℙ a b) ⟩
openIintervalℙ a b =
  ∩-openPred (pred> a) (pred< b) (openPred< a) (openPred> b)


IsContinuousWithPred⊆ : ∀ (P P' : ℝ → hProp ℓ-zero) f
  → (P'⊆P : P' ⊆ P)
  → IsContinuousWithPred P f
  → IsContinuousWithPred P' ((_∘ P'⊆P _) ∘ f)
IsContinuousWithPred⊆ P P' f P'⊆P fC u ε u∈P =
  PT.map (map-snd ((_∘ P'⊆P _) ∘_)) (fC u ε (P'⊆P _ u∈P))


≡ContinuousWithPred : ∀ P P' → ⟨ openPred P ⟩ → ⟨ openPred P' ⟩ → ∀ f g
  → IsContinuousWithPred P f
  → IsContinuousWithPred P' g
  → (∀ r r∈ r∈' → f (rat r) r∈ ≡ g (rat r) r∈')
  → ∀ u u∈ u∈' → f u u∈ ≡ g u u∈'
≡ContinuousWithPred P P' oP oP' f g fC gC e = Elimℝ-Prop.go w
 where
 w : Elimℝ-Prop
   (λ z → (u∈ : ⟨ P z ⟩) (u∈' : ⟨ P' z ⟩) → f z u∈ ≡ g z u∈')
 w .Elimℝ-Prop.ratA = e
 w .Elimℝ-Prop.limA x xC R x∈ x∈' = PT.rec2 (isSetℝ _ _)
   (λ (Δ , PΔ) (Δ' , PΔ') → eqℝ _ _ λ ε₀ →
     let ε = ε₀
         f' = fC (lim x xC) (ε /2₊) x∈
         g' = gC (lim x xC) (ε /2₊) x∈'
     in PT.rec2
       (isProp∼ _ _ _)
       (λ (θ , θ∼) (η , η∼) →
         let δ = min₊ (min₊ Δ Δ') (min₊ θ η) /2₊
             limX∼x = sym∼ _ _ _ (𝕣-lim-self x xC δ δ)
             xδ∈P : ⟨ P (x δ) ⟩
             xδ∈P = PΔ (x δ)
               (∼-monotone≤
                 (subst (ℚ._≤ fst Δ) ℚ!!
                   (ℚ.isTrans≤ _ _ _
                     (ℚ.min≤ (fst (min₊ Δ Δ')) (fst (min₊ θ η)))
                     (ℚ.min≤ (fst Δ) (fst Δ'))))
                 limX∼x)
             xδ∈P' : ⟨ P' (x δ) ⟩
             xδ∈P' = PΔ' (x δ)
               (∼-monotone≤
                 (subst (ℚ._≤ fst Δ') ℚ!!
                   (ℚ.isTrans≤ _ _ _
                     (ℚ.min≤ (fst (min₊ Δ Δ')) (fst (min₊ θ η)))
                     (ℚ.min≤' (fst Δ) (fst Δ'))))
                 limX∼x)
             zF : f (lim x xC) x∈ ∼[ ε /2₊ ] g (x δ) xδ∈P'
             zF = subst (f (lim x xC) x∈ ∼[ ε /2₊ ]_)
               (R _ xδ∈P xδ∈P')
               (θ∼ _ _
                 (∼-monotone≤
                   (subst (ℚ._≤ fst θ) ℚ!!
                     (ℚ.isTrans≤ _ _ _
                       (ℚ.min≤' (fst (min₊ Δ Δ')) (fst (min₊ θ η)))
                       (ℚ.min≤ (fst θ) (fst η))))
                   (sym∼ _ _ _ (𝕣-lim-self x xC δ δ))))
             zG : g (lim x xC) x∈' ∼[ ε /2₊ ] g (x δ) xδ∈P'
             zG = η∼ _ _
               (∼-monotone≤
                 (subst (ℚ._≤ fst η) ℚ!!
                   (ℚ.isTrans≤ _ _ _
                     (ℚ.min≤' (fst (min₊ Δ Δ')) (fst (min₊ θ η)))
                     (ℚ.min≤' (fst θ) (fst η))))
                 (sym∼ _ _ _ (𝕣-lim-self x xC δ δ)))
         in subst∼ ℚ!! (triangle∼ zF (sym∼ _ _ _ zG)))
       f' g')
   (oP (lim x xC) x∈) (oP' (lim x xC) x∈')
 w .Elimℝ-Prop.isPropA _ = isPropΠ2 λ _ _ → isSetℝ _ _


-- Previous location: Continuity.Base.
sym-intervalℙ⊆ointervalℙ : ∀ a b → a <ᵣ b →
  intervalℙ (-ᵣ a) a ⊆ ointervalℙ (-ᵣ b) b
sym-intervalℙ⊆ointervalℙ a b a<b =
  intervalℙ⊆ointervalℙ _ _ _ _ (-ᵣ<ᵣ _ _ a<b) a<b
