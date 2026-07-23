
module Cubical.HITs.CauchyReals.Analysis.Lipschitz.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sum as ⊎
import Cubical.Data.Int.Fast as ℤ
import Cubical.Data.Int.Fast.Order as ℤ
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.HITs.PropositionalTruncation as PT


open import Cubical.Data.NatPlusOne
open import Cubical.Data.Nat

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.Tactics.CauchyReals.ExpressionLifting

open import Cubical.HITs.CauchyReals.Foundation.Rationals

open ℚ

opaque
 sΣℚ< : ∀ {u v ε ε'} → fst ε ≡ ε' → (u ∼[ ε ] v) →
          Σ (0< ε') (λ z → u ∼[ ε' , z ] v)
 sΣℚ< {u} {v} {ε} p x =
    subst (λ ε' → Σ (0< ε') (λ z → u ∼[ ε' , z ] v)) p (snd ε , x)

 sΣℚ<' : ∀ {u v ε ε'} → fst ε ≡ ε' → (u ∼'[ ε ] v) →
          Σ (0< ε') (λ z → u ∼'[ ε' , z ] v)
 sΣℚ<' {u} {v} {ε} p x =
    subst (λ ε' → Σ (0< ε') (λ z → u ∼'[ ε' , z ] v)) p (snd ε , x)

-- 11.3.36
𝕣-lim : ∀ r y ε δ p →
          r ∼[ ε ] ( y δ )
        → r ∼[ ε +₊ δ  ] (lim y p )
𝕣-lim = Elimℝ-Prop.go w

 where
 w : Elimℝ-Prop _
 w .Elimℝ-Prop.ratA x y ε δ p x₁ =
   rat-lim x y (ε +₊ δ) δ p (subst 0<_ ℚ!! (snd ε))
    (subst∼ ℚ!! x₁)
 w .Elimℝ-Prop.limA x p R y ε δ p₁ = PT.rec (isProp∼ _ _ _)
     (uncurry λ θ → PT.rec (isProp∼ _ _ _) (uncurry $ λ vv →
        uncurry (lim-lim _ _ _ ( θ /4₊) δ _ _) ∘
                  (sΣℚ< ℚ!! ∘
                    (triangle∼ (R ( θ /4₊) x ( θ /2₊)
                      ( θ /4₊) p (refl∼ _ _)))))) ∘ fst (rounded∼ _ _ _)

 w .Elimℝ-Prop.isPropA _ = isPropΠ5 λ _ _ _ _ _ → isProp∼ _ _ _


-- 11.3.37
𝕣-lim-self : ∀ x y δ ε → x δ ∼[ δ +₊ ε ] lim x y
𝕣-lim-self x y δ ε =
 subst∼ ℚ!! $ 𝕣-lim (x δ) x (δ +₊  ε /2₊) (( ε /2₊)) y
  (y δ ( ε /2₊))

-- 11.3.36
𝕣-lim' : ∀ r y ε δ p v →
          r ∼[ fst ε ℚ.- fst δ , v ] ( y δ )
        → r ∼[ ε ] (lim y p )
𝕣-lim' r y ε δ p v₁ x =
   subst∼ ℚ!!
     $ 𝕣-lim r y (fst ε ℚ.- fst δ , v₁) δ p x

-- HoTT Lemma (11.3.10)
lim-surj : ∀ r → ∃[ x ∈ _ ] (r ≡ (uncurry lim x) )
lim-surj = PT.map (map-snd (eqℝ _ _)) ∘ (Elimℝ-Prop.go w)
 where
 w : Elimℝ-Prop λ x → ∃[ _ ∈ _ ] _
 w .Elimℝ-Prop.ratA x =
    ∣ ((λ _ → rat x) , (λ _ _ → refl∼ _ _)) ,
      (λ ε → 𝕣-lim' _ _ _ (ε /2₊) _ <≤ℚ! (refl∼ _ _) ) ∣₁


 w .Elimℝ-Prop.limA x p _ = ∣ (x , p) , refl∼ _ ∣₁
 w .Elimℝ-Prop.isPropA _ = squash₁


Lipschitz-ℚ→ℚ : ℚ₊ → (ℚ → ℚ) → Type
Lipschitz-ℚ→ℚ L f =
  (∀ q r → (ε : ℚ₊) →
    abs (q ℚ.- r) ℚ.< (fst ε) → abs (f q ℚ.- f r) ℚ.< fst (L ·₊ ε  ))


Lipschitz-ℚ→ℚ' : ℚ₊ → (ℚ → ℚ) → Type
Lipschitz-ℚ→ℚ' L f =
  ∀ q r →
    abs (f q ℚ.- f r) ℚ.≤ fst L ℚ.· abs (q ℚ.- r)

Lipschitz-ℚ→ℚ'→Lipschitz-ℚ→ℚ : ∀ L f →
 Lipschitz-ℚ→ℚ' L f → Lipschitz-ℚ→ℚ L f
Lipschitz-ℚ→ℚ'→Lipschitz-ℚ→ℚ L f P q r ε <ε =
  ℚ.isTrans≤< _ _ _ (P q r)
    (ℚ.<-o· (abs (q ℚ.- r)) (fst ε) _ (snd L) <ε)


Lipschitz-ℚ→ℚ-restr : ℚ₊ → ℚ₊ → (ℚ → ℚ) → Type
Lipschitz-ℚ→ℚ-restr Δ L f =
  (∀ q r → abs q ℚ.< fst Δ → abs r ℚ.< fst Δ → (ε : ℚ₊) →
    abs (q ℚ.- r) ℚ.< (fst ε) → abs (f q ℚ.- f r) ℚ.< fst (L ·₊ ε  ))

Lipschitz-ℚ→ℚ-restr' : ℚ₊ → ℚ₊ → (ℚ → ℚ) → Type
Lipschitz-ℚ→ℚ-restr' Δ L f =
  (∀ q r → fst Δ ℚ.< abs q → fst Δ  ℚ.< abs r → (ε : ℚ₊) →
    abs (q ℚ.- r) ℚ.< (fst ε) → abs (f q ℚ.- f r) ℚ.< fst (L ·₊ ε  ))


Lipschitz-ℚ→ℚ-extend : ∀ Δ L f (δ : ℚ₊) → fst δ ℚ.< fst Δ
 → Lipschitz-ℚ→ℚ-restr Δ L f
 → Lipschitz-ℚ→ℚ L (f ∘ ℚ.clamp (ℚ.- (fst Δ ℚ.- fst δ)) (fst Δ ℚ.- fst δ))
Lipschitz-ℚ→ℚ-extend Δ L f δ δ<Δ x q r ε v =
 let z : ∀ u → abs (ℚ.clamp (ℚ.- (fst Δ ℚ.- fst δ)) (fst Δ ℚ.- fst δ) u)
                  ℚ.< fst Δ
     z u = absFrom<×< (fst Δ)
              (ℚ.clamp (ℚ.- (fst Δ ℚ.- fst δ)) (fst Δ ℚ.- fst δ) u)
               (ℚ.isTrans<≤ (ℚ.- (fst Δ)) (ℚ.- (fst Δ ℚ.- fst δ)) _
                 (subst2 (ℚ._<_) ℚ!! ℚ!!
                     ((ℚ.<-o+ 0 (fst δ) (ℚ.- (fst Δ)) (snd δ))))
                 (ℚ.≤clamp (ℚ.- (fst Δ ℚ.- fst δ)) (fst Δ ℚ.- fst δ) u
                    (<≤ℚ![ δ<Δ ] )) )
               (ℚ.isTrans≤< _ _ _ (clamp≤ (ℚ.- (fst Δ ℚ.- fst δ)) _ u) <≤ℚ!)

 in x (ℚ.clamp (ℚ.- (fst Δ ℚ.- fst δ)) (fst Δ ℚ.- fst δ) q)
            (ℚ.clamp (ℚ.- (fst Δ ℚ.- fst δ)) (fst Δ ℚ.- fst δ) r)
            (z q) (z r) ε
             (ℚ.isTrans≤< _ _ _
               (ℚ.clampDist (ℚ.- (fst Δ ℚ.- fst δ)) (fst Δ ℚ.- fst δ) r q)
               v)


-- HoTT Definition (11.3.14)
Lipschitz-ℚ→ℝ : ℚ₊ → (ℚ → ℝ) → Type
Lipschitz-ℚ→ℝ L f =
  (∀ q r → (ε : ℚ₊) →
    (ℚ.- (fst ε)) ℚ.< (q ℚ.- r)
     → q ℚ.- r ℚ.< (fst ε) → f q ∼[ L ·₊ ε  ] f r)

Lipschitz-rat∘ : ∀ l f → Lipschitz-ℚ→ℚ l f → Lipschitz-ℚ→ℝ l (rat ∘ f)
Lipschitz-rat∘ l f x =
  λ q r ε x₁ x₂ →
    rat-rat-fromAbs _ _ _
       $ x q r ε (absFrom<×< (fst ε) (q ℚ.- r) x₁ x₂)

Lipschitz-ℝ→ℝ : ℚ₊ → (ℝ → ℝ) → Type
Lipschitz-ℝ→ℝ L f =
  (∀ u v → (ε : ℚ₊) →
    u ∼[ ε  ] v → f u ∼[ L ·₊ ε  ] f v)


isPropLipschitz-ℝ→ℝ : ∀ q f → isProp (Lipschitz-ℝ→ℝ q f)
isPropLipschitz-ℝ→ℝ q f = isPropΠ4 λ _ _ _ _ → isProp∼ _ _ _

·- : ∀ x y → x ℚ.· (ℚ.- y) ≡ ℚ.- (x ℚ.· y)
·- x y = ℚ.·Assoc x (-1) y
         ∙∙ cong (ℚ._· y) (ℚ.·Comm x (-1))
         ∙∙ sym (ℚ.·Assoc (-1) x y)


NonExpandingₚ : (ℝ → ℝ) → hProp ℓ-zero
fst (NonExpandingₚ f) = ∀ u v ε →  u ∼[ ε ] v → f u ∼[ ε ] f v
snd (NonExpandingₚ f) = isPropΠ4 λ _ _ _ _ → isProp∼ _ _ _



NonExpandingℚ→ℝₚ : (ℚ → ℝ) → hProp ℓ-zero
fst (NonExpandingℚ→ℝₚ f) = ∀ u v ε → rat u ∼[ ε ] rat v → (f u) ∼[ ε ]  (f v)
snd (NonExpandingℚ→ℝₚ f) = isPropΠ4 λ _ _ _ _ → isProp∼ _ _ _


NonExpandingGo :  Σ (ℚ → ℝ) (fst ∘ NonExpandingℚ→ℝₚ) → Σ _ (fst ∘ NonExpandingₚ)
NonExpandingGo (f , fL) = f' ,
  λ u v ε x → Elimℝ.go∼ w x
 where

 rl : _
 rl q y ε δ p v r v' u' z =
  𝕣-lim' (f q) (v')
            (ε) (δ)
          u'
          v
          z

 w : Elimℝ (λ _ → ℝ) λ u v ε _ → u ∼[  ε  ] v
 w .Elimℝ.ratA = f
 w .Elimℝ.limA x p a v = lim (a) v

 w .Elimℝ.eqA p a a' x y = eqℝ a a' y

 w .Elimℝ.rat-rat-B q r ε x x₁ = fL q r ε (rat-rat q r ε x x₁)
 w .Elimℝ.rat-lim-B = rl
 w .Elimℝ.lim-rat-B x r ε δ p v₁ u v' u' x₁ = sym∼ _ _ _ $
  rl r x ε δ p v₁ (sym∼ _ _ _ u) v' u' (sym∼ _ _ _ x₁)
 w .Elimℝ.lim-lim-B x y ε δ η p p' v₁ r v' u' v'' u'' x₁ =
  lim-lim v' v'' ε δ η u' u'' v₁ x₁

 w .Elimℝ.isPropB _ _ _ _ = isProp∼ _ _ _



 f' : ℝ → ℝ
 f' = Elimℝ.go w


fromLipschitzGo : ∀ L → Σ _ (Lipschitz-ℚ→ℝ L) → Σ _ (Lipschitz-ℝ→ℝ L)
fromLipschitzGo L (f , fL) = f' ,
  λ u v ε x → Elimℝ.go∼ w x
 where

 opaque
  lip-prf : ∀ (a : ℚ₊ → ℝ) (v : (δ ε : ℚ₊) → a δ ∼[ L ·₊ (δ +₊ ε) ] a ε)
   → (δ ε : ℚ₊) → a (L ⁻¹₊ ·₊ δ) ∼[ δ +₊ ε ] a (L ⁻¹₊ ·₊ ε)
  lip-prf a v δ ε =
       let v' = v (((L ⁻¹₊)  ·₊ δ)) (((L ⁻¹₊) ·₊ ε))
       in subst (λ q → a ((L ⁻¹₊) ·₊ δ) ∼[ q ] a ((L ⁻¹₊) ·₊ ε))
           (ℚ₊≡ ℚ!) v'

 rl : _
 rl q y ε δ p v r v' u' z =
  𝕣-lim' (f q) (v' ∘ ((L ⁻¹₊) ·₊_))
            (L ·₊ ε) (L ·₊ δ)
          (lip-prf v' u')
          (subst 0<_ ( ℚ!! )
            (ℚ.·0< (fst L) (fst ε ℚ.- fst δ) (snd L) v) )
              (subst2 (f q ∼[_]_) (ℚ₊≡ ℚ!!)
                 (cong v' (ℚ₊≡ ℚ!)) z)

 w : Elimℝ (λ _ → ℝ) λ u v ε _ → u ∼[ L ·₊ ε  ] v
 w .Elimℝ.ratA = f
 w .Elimℝ.limA x p a v = lim (a ∘ ((L ⁻¹₊) ·₊_))
   (lip-prf a v)

 w .Elimℝ.eqA p a a' x y =
   eqℝ a a' λ ε →
     subst (λ q → a ∼[ q ] a') (ℚ₊≡ ℚ!)
                        (y ((L ⁻¹₊) ·₊ ε))
 w .Elimℝ.rat-rat-B q r ε x x₁ = fL q r ε x x₁
 w .Elimℝ.rat-lim-B = rl
 w .Elimℝ.lim-rat-B x r ε δ p v₁ u v' u' x₁ = sym∼ _ _ _ $
  rl r x ε δ p v₁ (sym∼ _ _ _ u) v' u' (sym∼ _ _ _ x₁)
 w .Elimℝ.lim-lim-B x y ε δ η p p' v₁ r v' u' v'' u'' x₁ =
  let e = ℚ!!
  in lim-lim _ _ _ (L ·₊ δ) (L ·₊ η) _ _
       (subst (0<_) e
         $ ℚ.·0< (fst L) (fst ε ℚ.- (fst δ ℚ.+ fst η))
              (snd L) v₁)

        ((cong v' (ℚ₊≡ ℚ!)
          subst∼[ ℚ₊≡ e ]
           cong v'' (ℚ₊≡ ℚ!)) x₁)
 w .Elimℝ.isPropB _ _ _ _ = isProp∼ _ _ _



 f' : ℝ → ℝ
 f' = Elimℝ.go w

opaque
 fromLipschitz : ∀ L → Σ _ (Lipschitz-ℚ→ℝ L) → Σ _ (Lipschitz-ℝ→ℝ L)
 fromLipschitz = fromLipschitzGo


 fromLipschitz-rat : ∀ {L lf q} → fst (fromLipschitz L lf) (rat q) ≡ fst lf q
 fromLipschitz-rat = refl

 fromLipschitz-lim : ∀ {L lf x y y'}  → fst (fromLipschitz L lf) (lim x y) ≡
                          lim ((fst (fromLipschitz L lf) ∘ x) ∘ (((L ⁻¹₊)) ·₊_)) y'
 fromLipschitz-lim {y = y} {y'} =
   cong (lim _) (isPropΠ2 (λ _ _ → isProp∼ _ _ _) _ y')



∼-monotone< : ∀ {u v ε 0<ε ε' 0<ε'} → ε ℚ.< ε'
  → u ∼[ ε , 0<ε ] v → u ∼[ ε' , 0<ε' ] v
∼-monotone< {u} {v} {ε} {_} {ε'} x x₁ =
  subst∼ ℚ!!
   (triangle∼ x₁ (refl∼ v
    ((ε' ℚ.- ε) , <≤ℚ![ x ])))

∼-monotone≤ : ∀ {u v ε 0<ε ε' 0<ε'} →
   ε ℚ.≤ ε' → u ∼[ ε , 0<ε ] v → u ∼[ ε' , 0<ε' ] v
∼-monotone≤ {u} {v} {ε} {_} {ε'} x x₁ =
   ⊎.rec (flip subst∼ x₁ )
         (flip ∼-monotone< x₁ )
     $ ℚ.≤→<⊎≡ ε ε' x


lipschConstIrrel : ∀ L₁ L₂ (x : ℚ₊ → ℝ) → ∀  p₁ p₂ →
         lim (λ q → x (L₁ ·₊ q)) p₁
       ≡ lim (λ q → x (L₂ ·₊ q)) p₂
lipschConstIrrel L₁ L₂ =
   ⊎.rec (w L₁ L₂) (λ x x₁ p₁ p₂ →
     sym (w L₂ L₁ x x₁ p₂ p₁)) (ℚ.getPosRatio L₁ L₂)


 where
 w : ∀ L₁ L₂ → (fst (((L₁ ⁻¹₊)) ·₊  L₂)) ℚ.≤ [ 1 / 1+ 0 ] →
      (x : ℚ₊ → ℝ)
      (p₁ : (δ ε : ℚ₊) → x (L₁ ·₊ δ) ∼[ δ +₊ ε ] x (L₁ ·₊ ε))
      (p₂ : (δ ε : ℚ₊) → x (L₂ ·₊ δ) ∼[ δ +₊ ε ] x (L₂ ·₊ ε)) →
      lim (λ q → x (L₁ ·₊ q)) p₁ ≡ lim (λ q → x (L₂ ·₊ q)) p₂
 w L₁ L₂ L₂/L₁≤1 x p₁ p₂ = eqℝ _ _ $ λ ε →

    (
      (uncurry (lim-lim _ _ ε (ε /4₊) (ε /4₊) p₁ p₂)
         (sΣℚ< ℚ!! (( refl subst∼[ refl ] cong x
               (ℚ₊≡ ℚ!)) $
            (∼-monotone≤ {0<ε' = snd ((ε /4₊) +₊ (1 ·₊ (ε /4₊)))}
               ((ℚ.≤-o+ _ (1 ℚ.· (fst (ε /4₊))) (fst (ε /4₊))
                 (ℚ.≤-·o (fst ((L₁ ⁻¹₊) ·₊ L₂)) 1 (fst (ε /4₊))
                  (ℚ.0≤ℚ₊ (ε /4₊)) L₂/L₁≤1)))
               $ p₁ (ε /4₊) (((L₁ ⁻¹₊) ·₊ L₂) ·₊ ε /4₊))))))


NonExpandingℚₚ : (ℚ → ℚ) → hProp ℓ-zero
fst (NonExpandingℚₚ f) = ∀ q r → abs (f q ℚ.- f r) ℚ.≤ abs (q ℚ.- r)
snd (NonExpandingℚₚ f) = isPropΠ2 λ _ _ → ℚ.isProp≤ _ _

NonExpandingₚ∘ : ∀ f g → ⟨ NonExpandingₚ f ⟩ → ⟨ NonExpandingₚ g ⟩ →
                    ⟨ NonExpandingₚ (f ∘ g) ⟩
NonExpandingₚ∘ _ _ x y _ _ _ = x _ _ _ ∘ (y _ _ _)


congLim : ∀ x y x' y' → (∀ q → x q ≡ x' q) → lim x y ≡ lim x' y'
congLim x y x' y' p =
  congS (uncurry lim)
          (Σ≡Prop (λ _ → isPropΠ2 λ _ _ → isProp∼ _ _ _)
           (funExt p))


-- open ℚ.HLP

congLim' : ∀ x y x' → (p : ∀ q → x q ≡ x' q) →
 lim x y ≡ lim x' (subst (λ x' → (δ ε : ℚ₊) → x' δ ∼[ δ +₊ ε ] x' ε)
                      (funExt p) y)
congLim' x y x' p =
   congLim x y x' _ p

-- HoTT Lemma (11.3.40)
record NonExpanding₂ (g : ℚ → ℚ → ℚ ) : Type where
 -- no-eta-equality

 field

  cL : ∀ q r s →
       abs (g q s ℚ.- g r s) ℚ.≤ abs (q ℚ.- r)

  cR : ∀ q r s →
      (abs (g q r ℚ.- g q s) ℚ.≤ abs (r ℚ.- s))




 zz : (q : ℚ) → Σ (ℝ → ℝ) ((λ r → fst r) ∘ NonExpandingₚ)
 zz q = NonExpandingGo (rat ∘ g q ,
     λ u v ε x → rat-rat-fromAbs _ _ _ (ℚ.isTrans≤< _ _ _ (cR q u v)
       let o , oo = ∼→∼' _ _ _ x
        in absFrom<×< (fst ε) (u - v) o oo)  )


 w : Elimℝ
       _ λ h h' ε v → ∀ u → (fst h u) ∼[ ε ] fst h' u
 w .Elimℝ.ratA x .fst = fst (zz x)

 w .Elimℝ.ratA x .snd ε u v = snd (zz x) u v ε

 w .Elimℝ.limA x p a x₁ .fst u =
   lim (λ q → fst (a q) u) λ δ ε → x₁ δ ε u
 w .Elimℝ.limA x p a x₁ .snd ε u v =
   PT.rec (isProp∼ _ _ _)
     (uncurry λ q → PT.rec (isProp∼ _ _ _)
       λ (xx , xx') →
        let q/2 =  q /2₊
            z = snd (a q/2) _ _ _ xx'
        in lim-lim _ _ _ q/2 q/2 _ _
             (subst 0<_ ℚ!! xx)
             (subst∼ ℚ!! z))
     ∘S fst (rounded∼ _ _ _)

 w .Elimℝ.eqA p a a' x x₁ = Σ≡Prop
   (λ _ → isPropΠ4 λ _ _ _ _ → isProp∼ _ _ _)
   (funExt λ rr →
     eqℝ _ _ λ ε → x₁ ε rr)
 w .Elimℝ.rat-rat-B q r ε x x₁ u =
    Elimℝ-Prop.go rr u ε x x₁

  where
  rr :  Elimℝ-Prop λ u → (ε : ℚ₊) (x : (ℚ.- fst ε) ℚ.< (q ℚ.- r))
         (x₁ : (q ℚ.- r) ℚ.< fst ε) →
               fst (zz q) u ∼[ ε ] fst (zz r) u
  rr .Elimℝ-Prop.ratA qq ε x₁ x₂ =
    rat-rat-fromAbs _ _ _
      (ℚ.isTrans≤<
        (abs (g q qq ℚ.- g r qq))
        (abs (q ℚ.- r))
        _
        (cL q r qq) (absFrom<×< (fst ε) (q ℚ.- r) x₁ x₂))

  rr .Elimℝ-Prop.limA x p x₁ ε x₂ x₃ = limA-prf

   where
    limA-prf : fst (zz q) (lim x p) ∼[ ε ] fst (zz r) (lim x p)
    limA-prf =
      let ((θ , θ<) , (x₂' , x₃'))  = getθ ε ((q ℚ.- r)) (x₂ , x₃)
          θ/2 =  (θ , θ<) /2₊
          zzz : fst (zz q) (x θ/2) ∼[ (fst ε ℚ.- θ) , x₂' ]
                 fst (zz r) (x θ/2)
          zzz = x₁ θ/2  ((fst ε ℚ.- θ) , x₂') (fst x₃') (snd x₃')
      in lim-lim _ _ _ θ/2 θ/2
                  _ _
                   ((subst {x = fst ε ℚ.- θ}
                          {y = fst ε ℚ.- ((fst θ/2 ℚ.+ fst θ/2))}
                         (0 <_) ℚ!! x₂'))
                                ((subst2 (λ xx yy → fst (zz q) (x xx) ∼[ yy ]
                       fst (zz r) (x xx))
                         refl
                         (ℚ₊≡ ℚ!!) zzz))
  rr .Elimℝ-Prop.isPropA _ = isPropΠ3 λ _ _ _ → isProp∼ _ _ _

 w .Elimℝ.rat-lim-B _ _ ε δ _ _ _ _ _ x _ =
       subst∼ (sym $ ℚ!!) $ 𝕣-lim _ _ _ _ _ (x _)
 w .Elimℝ.lim-rat-B _ _ ε δ _ _ _ _ _ x₁ _ =
   subst∼ (sym $ ℚ!!)
    $ sym∼ _ _ _ (𝕣-lim _ _ _ _ _ (sym∼ _ _ _ $ x₁ _))
 w .Elimℝ.lim-lim-B _ _ _ _ _ _ _ _ _ _ _ _ _ x₁ _ =
   lim-lim _ _ _ _ _ _ _ _ (x₁ _)
 w .Elimℝ.isPropB a a' ε _ = isPropΠ λ _ → isProp∼ _ _ _

 opaque
  preF : ℝ → Σ (ℝ → ℝ) λ h → ∀ ε u v → u ∼[ ε ] v → h u ∼[ ε ] h v
  preF = Elimℝ.go w


  go : ℝ → ℝ → ℝ
  go x = fst (preF x)

  go-rat-rat : ∀ x y → go (rat x) (rat y) ≡ rat (g x y)
  go-rat-rat _ _ = refl

  go∼R : ∀ x u v ε → u ∼[ ε ] v → go x u ∼[ ε ] go x v
  go∼R x u v ε = snd (preF x) ε u v

  go∼L : ∀ x u v ε → u ∼[ ε ] v → go u x ∼[ ε ] go v x
  go∼L x u v ε y = Elimℝ.go∼ w {u} {v} {ε} y x


  go∼₂ : ∀ δ η {u v u' v'} → u ∼[ δ  ] v → u' ∼[ η ] v'
              → go u u' ∼[ δ +₊ η ] go v v'
  go∼₂ δ η {u} {v} {u'} {v'} x x' =
    (triangle∼ (go∼L u' u v _ x) (go∼R v u' v' _ x'))


  β-rat-lim : ∀ r x y y' → go (rat r) (lim x y) ≡
                          lim (λ q → go (rat r) (x q))
                           y'
  β-rat-lim r x y y' = congLim _ _ _ _
    λ q → cong (go (rat r) ∘ x)
      (ℚ₊≡ ℚ!!)


  β-rat-lim' : ∀ r x y → Σ _
             λ y' → (go (rat r) (lim x y) ≡
                          lim (λ q → go (rat r) (x q)) y')
  β-rat-lim' r x y = _ , congLim' _ _ _
    λ q → cong (go (rat r) ∘ x)
      (ℚ₊≡ ℚ!!)


  β-lim-lim/2 : ∀ x y x' y' → Σ _ (λ yy' → go (lim x y) (lim x' y') ≡
                          lim (λ q → go (x ( q /2₊)) (x' ( q /2₊)))
                           yy')
  β-lim-lim/2 x y x' y' =
    let
        zz : lim (λ q → fst (Elimℝ.go w (x q)) (lim x' y'))
               (λ δ ε → Elimℝ.go∼ w (y δ ε) (lim x' y')) ≡
             lim (λ q → fst (Elimℝ.go w (x ( q /2₊))) (x' ( q /2₊)))
                    λ δ ε →
                     subst∼ ℚ!! $
                        triangle∼
                         (go∼R (x ( δ /2₊))  (x' ( δ /2₊)) (x' (ε /2₊))
                          ( δ /2₊ +₊ ε /2₊)
                           (y' _ _))
                          (go∼L (x' (ε /2₊))
                           (x ( δ /2₊)) (x (ε /2₊)) _ (y _ _))
        zz = eqℝ (lim (λ q → fst (Elimℝ.go w (x q)) (lim x' y'))
                  (λ δ ε → Elimℝ.go∼ w (y δ ε) (lim x' y')))
                 _
               (λ ε →
                let ε/4 = ε /4₊



                in (lim-lim _ (λ q' → go (x ( q' /2₊)) (x' ( q' /2₊))) ε
                         ((ε /2₊) /4₊) ε/4 (λ δ ε₁ → Elimℝ.go∼ w (y δ ε₁) (lim x' y'))
                           _) <≤ℚ!
                         ((go∼R ( x (ε /2₊ /4₊)) (lim x' y')
                           (x' (ε /2₊ /4₊)) _
                           ((∼-monotone<
                              {ε = (((ε /2₊) /4₊) +₊ ((ε /2₊) /4₊)) .fst}
                              {ε' = fst ε ℚ.- (fst ((ε /2₊) /4₊) ℚ.+ fst ε/4)}
                                <≤ℚ! $ sym∼ _ _ _ (𝕣-lim-self x' y'
                              (ε /2₊ /4₊) (ε /2₊ /4₊)))))))
    in _ , zz


  isLiftOfNonExpanding₂ : go isLiftOf₂ g
  isLiftOfNonExpanding₂ ._isLiftOf₂_.prf _ _ = refl

opaque
 NonExpanding₂-flip : ∀ g → NonExpanding₂ g → NonExpanding₂ (flip g)
 NonExpanding₂-flip g ne .NonExpanding₂.cL q r s =
    NonExpanding₂.cR ne s q r
 NonExpanding₂-flip g ne .NonExpanding₂.cR q r s =
    NonExpanding₂.cL ne r s q



isPropNonExpanding₂ : ∀ g → isProp (NonExpanding₂ g)
isPropNonExpanding₂ g x y i .NonExpanding₂.cL =
  isPropΠ3 (λ q r s →
   ℚ.isProp≤ (abs (g q s ℚ.- g r s)) (abs (q ℚ.- r)))
     (λ q r s → x .NonExpanding₂.cL q r s)
    (λ q r s → y .NonExpanding₂.cL q r s) i
isPropNonExpanding₂ g x y i .NonExpanding₂.cR =
   isPropΠ3 (λ q r s →
   ℚ.isProp≤ (abs (g q r ℚ.- g q s)) (abs (r ℚ.- s)))
     (λ q r s → x .NonExpanding₂.cR q r s)
    (λ q r s → y .NonExpanding₂.cR q r s) i

opaque
 nonExpanding₂Ext : (g g' : _)
    → (ne : NonExpanding₂ g) (ne' : NonExpanding₂ g')
    → (∀ x y → g x y ≡ g' x y)
    → ∀ x y → NonExpanding₂.go ne x y  ≡ NonExpanding₂.go ne' x y
 nonExpanding₂Ext g g' ne ne' p x y =
   congS (λ x₁ → NonExpanding₂.go (snd x₁) x y)
    (Σ≡Prop isPropNonExpanding₂ {_ , ne} {_ , ne'}
     λ i x₁ x₂ → p x₁ x₂ i)

opaque
 unfolding NonExpanding₂.go
 NonExpanding₂-flip-go : ∀ g → (ne : NonExpanding₂ g)
                               (flip-ne : NonExpanding₂ (flip g)) → ∀ x y →
      (NonExpanding₂.go {g = flip g} flip-ne x y)
    ≡ (NonExpanding₂.go {g = g} ne y x)
 NonExpanding₂-flip-go g ne flip-ne = Elimℝ-Prop2.go w
  where
  w : Elimℝ-Prop2
           λ z z₁ → NonExpanding₂.go flip-ne z z₁ ≡ NonExpanding₂.go ne z₁ z

  w .Elimℝ-Prop2.rat-ratA _ _ = refl
  w .Elimℝ-Prop2.rat-limA r x y x₁ =
    congLim _ _ _ _
      λ q → congS (NonExpanding₂.go flip-ne (rat r) ∘S x)
        ((ℚ₊≡ $ ℚ!! )) ∙ x₁ q

  w .Elimℝ-Prop2.lim-ratA x y r x₁ =
     congLim _ _ _ _
      λ q → x₁ q

  w .Elimℝ-Prop2.lim-limA x y x' y' x₁ =
       snd (NonExpanding₂.β-lim-lim/2 flip-ne
         x y x' y') ∙∙
          cong (uncurry lim)
           (Σ≡Prop (λ _ → isPropΠ2 λ _ _ → isProp∼ _ _ _)
            (funExt λ q → x₁ ( q /2₊) ( q /2₊)))
          ∙∙
        sym (snd (NonExpanding₂.β-lim-lim/2 ne
         x' y' x y))
  w .Elimℝ-Prop2.isPropA _ _ = isSetℝ _ _

reducedNonExpanding₂ : ∀ op → NonExpanding₂ op → NonExpanding₂ (λ q r → ℚ.reduce (op q r))
reducedNonExpanding₂ op = subst NonExpanding₂ (funExt₂ λ _ _ → reducedEqual _ )

module NonExpanding₂-Lemmas
        (g : ℚ → ℚ → ℚ)
        (ne : NonExpanding₂ g) where
 module NE = NonExpanding₂ ne

 module _ (gComm : ∀ p q → g p q ≡ g q p) where
  commLift₂ : ∀ x y → NE.go x y ≡ NE.go y x
  commLift₂ x y =
    nonExpanding₂Ext g (flip g)
     ne (NonExpanding₂-flip g ne) gComm x y ∙
   (NonExpanding₂-flip-go g ne
      (NonExpanding₂-flip g ne) x y )



 module _ (gComm : ∀ x y → NE.go x y ≡ NE.go y x)
          (gAssoc : ∀ p q r → g p (g q r) ≡ g (g p q) r)  where
  pp : ∀ ε → fst (ε /2₊) ≡ (fst ε ℚ.- (fst (ε /4₊) ℚ.+ fst (ε /4₊)))
  pp ε = ℚ!!

  opaque
   unfolding NonExpanding₂.go
   gAssoc∼ : ∀ x y z → ∀ ε → NE.go x (NE.go y z) ∼[ ε ] NE.go (NE.go x y) z
   gAssoc∼ = Elimℝ-Prop.go w
     where
     w : Elimℝ-Prop λ z →
                       (y z₁ : ℝ) (ε : ℚ₊) →
                       NE.go z (NE.go y z₁) ∼[ ε ] NE.go (NE.go z y) z₁
     w .Elimℝ-Prop.ratA q y z ε =
        subst2 (_∼[ ε ]_)
          (gComm (NE.go y z) (rat q))
          (λ i → NE.go (gComm y (rat q) i) z)
          (hh y z ε)
      where
      hh : (y z : ℝ) (ε : ℚ₊) →
             NE.go (NE.go y z) (rat q) ∼[ ε ] NE.go (NE.go y (rat q)) z
      hh = Elimℝ-Prop.go w'
        where
        w' : Elimℝ-Prop λ z₁ →
                           (z₂ : ℝ) (ε₁ : ℚ₊) →
                           NE.go (NE.go z₁ z₂) (rat q) ∼[ ε₁ ] NE.go (NE.go z₁ (rat q)) z₂
        w' .Elimℝ-Prop.ratA p = Elimℝ-Prop.go w''
          where
          w'' : Elimℝ-Prop λ z₁ →
                              (ε₁ : ℚ₊) →
                              NE.go (NE.go (rat p) z₁) (rat q) ∼[ ε₁ ]
                              NE.go (NE.go (rat p) (rat q)) z₁
          w'' .Elimℝ-Prop.ratA r ε = ≡→∼ (
           gComm (NE.go (rat p) (rat r)) (rat q) ∙∙ cong rat (gAssoc q p r)
            ∙∙ λ i → NE.go (gComm (rat q) (rat p) i) (rat r))
          w'' .Elimℝ-Prop.limA x x' R ε =
            subst2 (_∼[ ε ]_)
              (λ i → NE.go (gComm (lim x x')  (rat p)  i) (rat q))
              (sym (gComm (NE.go (rat p) (rat q)) (lim x x')))
             (hhh ε)
           where
           hhh : ∀ ε → NE.go (NE.go (lim x x') (rat p)) (rat q) ∼[ ε ]
                  NE.go (lim x x') (NE.go (rat p) (rat q))
           hhh ε =
            let zzz = R (ε /4₊) (ε /2₊)
            in uncurry (lim-lim _ _ ε (ε /4₊)
                (ε /4₊) _ _)
                 (sΣℚ< (pp ε)
                   ( (λ i → NE.go (gComm (rat p) (x (ε /4₊)) i) (rat q))
                       subst∼[ refl ] gComm (NE.go (rat p) (rat q))
                                           (x (ε /4₊))
                      $ zzz  ))

          w'' .Elimℝ-Prop.isPropA _ = isPropΠ λ _ → isProp∼ _ _ _
        w' .Elimℝ-Prop.limA x x' R z ε =
         uncurry (lim-lim _ _ ε (ε /4₊)
         (ε /4₊) _ _)
          (sΣℚ< (pp ε) (R (ε /4₊) z (ε /2₊) ))
        w' .Elimℝ-Prop.isPropA _ = isPropΠ2 λ _ _ → isProp∼ _ _ _

     w .Elimℝ-Prop.limA x x' R y z ε =
      uncurry (lim-lim _ _ ε (ε /4₊)
         (ε /4₊) _ _)
          (sΣℚ< (pp ε)
           (R (ε /4₊) y z (ε /2₊)))
     w .Elimℝ-Prop.isPropA _ = isPropΠ3 λ _ _ _ → isProp∼ _ _ _


fromLipshitzNEβ : ∀ f (fl : Lipschitz-ℚ→ℝ 1 f) x y {y'} →
  fst (fromLipschitz 1 (f , fl)) (lim x y) ≡
    lim (λ x₁ → ((fst (fromLipschitz 1 (f , fl)) ∘ x) ∘ _·₊_ 1) x₁)
     y'
fromLipshitzNEβ f fl x y {y'} = fromLipschitz-lim


fromLipshitzβLim : ∀ L f (fl : Lipschitz-ℚ→ℝ L f) x y {y'} →
  fst (fromLipschitz L (f , fl)) (lim x y) ≡
    lim (λ x₁ → fst (fromLipschitz L (f , fl)) (x ((L ⁻¹₊) ·₊ x₁)))
     y'
fromLipshitzβLim L f fl x y = fromLipschitz-lim

Lipschitz-ℝ→ℝℙ : ℚ₊ → (P : ℙ ℝ) → (∀ x → x ∈ P  → ℝ) → Type
Lipschitz-ℝ→ℝℙ L P f =
    (∀ u u∈ v v∈ → (ε : ℚ₊) →
        u ∼[ ε  ] v → f u u∈ ∼[ L ·₊ ε  ] f v v∈)
