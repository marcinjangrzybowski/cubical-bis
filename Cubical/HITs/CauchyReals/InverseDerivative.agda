module Cubical.HITs.CauchyReals.InverseDerivative where

{-
Legacy inverse-derivative proof for the old quotient-slope derivative API.
Previous exported name: invDerivativeℙ. It is intentionally commented while
the inverse derivative theorem is migrated to DerivativeOfℙ/uDerivativeOfℙ.

preMapLimitPos : ∀ P Q x x' f g y →
   (u : ∀ r r∈ ＃r →  g r r∈ ＃r ∈ Q)
   (v : ∀ r r∈ ＃r → x' ＃ g r r∈ ＃r)
  → at x  limitOfℙ P , g is x'
  → at x' limitOfℙ Q , f is y
  → at x  limitOfℙ P ,
   (λ r r∈ ＃r → f (g r r∈ ＃r) (u _ _ _) (v _ _ _ )) is y
preMapLimitPos _ _ _ _ _ _ _ _ _ gL =
  PT.rec squash₁
    (λ (δ , X) →
      PT.rec squash₁
       (λ (δ' , X') →
         ∣ δ' , (λ _ _ _ uu →
           let vv = X' _ _ _ uu
           in X _ _ _ vv) ∣₁)
       (gL δ)) ∘_

mapLimitPos' : ∀ x P Q f g y y∈ → (f∈ : ∀ r r∈ x＃ → f r r∈ x＃ ∈ Q)
  → IsContinuousWithPred Q g
  → at x limitOfℙ P , f is y
  → at x limitOfℙ P , (λ r r∈ x＃ → g (f r r∈ x＃) (f∈ _ _ _)) is
      g y y∈
mapLimitPos' x P Q f g y y∈ f∈ gC fL (ε , 0<ε) =
    PT.rec squash₁
    (λ (q , 0<q , q<ε) →
     let q₊ = (q , <ᵣ→<ℚ _ _ 0<q)
     in PT.rec squash₁
         (λ (δ' , D') →
            PT.rec squash₁
              (λ (δ , D) →
                ∣ minᵣ₊ (ℚ₊→ℝ₊ δ') δ ,
                    (λ r r∈ x＃r x-r<δ →
                       let uu = D r r∈ x＃r
                                  (isTrans<≤ᵣ _ _ _ x-r<δ
                                    (min≤ᵣ' (rat (fst δ')) _))
                           uu' = D' (f r r∈ x＃r) (f∈ r r∈ x＃r)
                                 (invEq (∼≃abs<ε _ _ _) uu)
                       in  isTrans<ᵣ _ _ _
                            (fst (∼≃abs<ε _ _ _) uu')
                            q<ε) ∣₁)
              (fL (ℚ₊→ℝ₊ (δ'))))
         (gC y (q₊) y∈))
   (denseℚinℝ _ _ 0<ε)

invDerivativeℙPos-temp : ∀ x f f' f'Pos (fPos : ∀ x 0<x → 0 <ᵣ f x 0<x )
  → (isEquivF : isEquiv {A = ℝ × Unit} {B = ℝ₊}
       λ x → f (fst x) (snd x) , fPos (fst x) (snd x) )
   → (∀ x y → fst x <ᵣ fst y →
       fst (invEq (_ , isEquivF) x) <ᵣ fst (invEq (_ , isEquivF) y))
   → (∀ x y → fst x <ᵣ fst y →
       (f (fst x) (snd x)) <ᵣ (f (fst y) (snd y)))
       → IsContinuousWithPred ⊤Pred f
  → IsContinuousWithPred pred0< (λ x x∈ → fst (invEq (_ , isEquivF) (x , x∈)))
  → derivativeOfℙ ⊤Pred , f at x is f'
  → derivativeOfℙ pred0< , (λ r 0<r →
       fst (invEq (_ , isEquivF) (r , 0<r)))
         at f (fst x) (snd x) , fPos _ _
       is fst (invℝ₊ (f' , f'Pos))
invDerivativeℙPos-temp x f f' f'Pos fPos isEquivF incrG incrF  fC gC dF =
  subst
    (uncurry (at (rat [ pos zero / 1+ zero ]) limitOfℙ_,_is
      fst (invℝ₊ (f' , f'Pos)) ))
    (ΣPathP (refl , funExt₃
      pp)) d''
  where

  e : _ ≃ _
  e = (_ , isEquivF)

  g = invEq e

  y = f (fst x) (snd x)

  h'' : (r : ℝ) → r ∈ (λ x₁ → pred0< (y +ᵣ x₁)) → ℝ
  h'' h h∈  = fst (g (_ , h∈)) -ᵣ fst x

  h' : (r : ℝ) → r ∈ (λ x₁ → pred0< (y +ᵣ x₁)) → 0 ＃ r → ℝ
  h' h h∈ _ = h'' h h∈

  uu : (r : ℝ) (r∈ : r ∈ (λ x₂ → pred0< (y +ᵣ x₂))) (＃r : 0 ＃ r) →
        h' r r∈ ＃r ∈ (λ x₂ → ⊤Pred (x .fst +ᵣ x₂))
  uu _ r∈ _ = tt

  vv : (r : ℝ) (r∈ : r ∈ (λ x₂ → pred0< (y +ᵣ x₂))) (＃r : 0 ＃ r) →
        0 ＃ h' r r∈ ＃r
  vv r r∈ = ⊎.elim
    (inl ∘ λ p → x<y→0<y-x _ _ (isTrans≡<ᵣ _ _ _
     (sym (cong fst (retEq e _)))
     (incrG (y , fPos _ _) _ (isTrans≡<ᵣ _ _ _ (sym (+IdR _))
       ((<ᵣ-o+ 0 _ y p))))) )
    (inr ∘ λ p →
      (x<y→x-y<0 _ _ (isTrans<≡ᵣ _ _ _
       (incrG _ _ (isTrans<≡ᵣ _ _ _ (<ᵣ-o+ _ 0 y p) (+IdR _)))
         (cong fst (retEq e _)))) )

  h-lim : at 0 limitOfℙ (λ x₁ → pred0< (y +ᵣ x₁)) , (λ h h∈ _ → h'' h h∈) is 0
  h-lim = subst (at _ limitOfℙ _ , h' is_) (Rℝ.+InvR' _ _
      (cong (fst ∘ invEq e) (ℝ₊≡ (+IdR y)) ∙ cong fst (retEq e _)))
    (IsContinuousLimℙ (λ x₁ → pred0< (y +ᵣ x₁)) h'' 0
      (isTrans<≡ᵣ _ _ _ (fPos (fst x) (snd x)) (sym (+IdR _)))

      (IsContinuousWP∘ ⊤Pred _ _ _ _
        (AsContinuousWithPred _ _ (IsContinuous+ᵣR (-ᵣ fst x)))
          (IsContinuousWP∘ _ _
               _ _ _ gC
           (AsContinuousWithPred _ _ (IsContinuous+ᵣL y ))))
           )

  d' : at 0 limitOfℙ (λ x₁ → pred0< (y +ᵣ x₁)) ,
        (λ r r∈ ＃r →
           differenceAtℙ ⊤Pred f (x .fst) (h' r r∈ ＃r) (vv r r∈ ＃r) (x .snd)
           (uu r r∈ ＃r))
        is f'
  d' = preMapLimitPos _ _ _ _ _
     h'
     f'
     uu vv
      h-lim dF

  h''-pos : (r : ℝ) (r∈ : r ∈ (λ x₁ → pred0< (f (fst x) (snd x) +ᵣ x₁)))
              (x＃ : 0 ＃ r) →
             0 <ᵣ differenceAtℙ ⊤Pred f (x .fst) (h' r r∈ x＃)
               _ (x .snd) _
  h''-pos r r∈ x＃ = incr→0<differenceAtℙ _ _ _ _ _ _ _
   λ _ _ _ _ → incrF _ _

  d'' :
   at 0 limitOfℙ pred0< ∘S (y +ᵣ_) ,
       (λ r z z₁ →
          fst (invℝ₊
            (differenceAtℙ ⊤Pred f (x .fst) (h' r z z₁) _ (x .snd) _ ,
             h''-pos r z z₁)))
         is (fst (invℝ₊ (f' , f'Pos)) )
  d'' = mapLimitPos' _ _ _ _ _ f'
          f'Pos
          h''-pos
          IsContinuousWithPred-invℝ₊
          d'

  pp : ∀ x' u v → fst (invℝ₊ (_ , _))
                   ≡ differenceAtℙ pred0< _
                      _ x' v (fPos (fst x) (snd x)) u
  pp x' u v =
    p0 ∙ p1 ∙ cong₂ _·ᵣ_ p2 p3 ∙ p4
   where
   h : ℝ
   h = h' x' u v

   h＃ : 0 ＃ h
   h＃ = vv x' u v

   Δ : ℝ
   Δ = f (x .fst +ᵣ h) (uu x' u v) -ᵣ f (x .fst) (x .snd)

   invh : ℝ
   invh = invℝ h h＃

   invx' : ℝ
   invx' = invℝ x' v

   gx' : ℝ
   gx' = fst (g (y +ᵣ x' , u))

   uuu : 0 <ᵣ Δ ·ᵣ invh
   uuu = h''-pos x' u v

   x+h≡gx' : x .fst +ᵣ h ≡ gx'
   x+h≡gx' = +ᵣComm (x .fst) h ∙ Rℝ.minusPlus gx' (x .fst)

   qq : f (x .fst +ᵣ h' x' u v) (uu x' u v) ≡ y +ᵣ x'
   qq = cong₂ f x+h≡gx' (toPathP refl)
         ∙ cong fst (secEq e (y +ᵣ x' , u))

   zzz : f (x .fst +ᵣ h' x' u v) (uu x' u v) -ᵣ f (x .fst) (x .snd)
              ≡ x'
   zzz =
     cong (_-ᵣ f (x .fst) (x .snd)) qq
       ∙ cong (_-ᵣ y) (+ᵣComm y x')
       ∙ Rℝ.plusMinus x' y

   zz : 0 ＃ ((f (x .fst +ᵣ h' x' u v) (uu x' u v)) -ᵣ f (x .fst) (x .snd))
   zz = subst (0 ＃_) (sym zzz) v

   Δ₊ : ℝ₊
   Δ₊ = absᵣ Δ , 0＃→0<abs Δ zz

   invh₊ : ℝ₊
   invh₊ = absᵣ invh , 0＃→0<abs invh (invℝ0＃ h h＃)

   Δg : ℝ
   Δg = fst (g (y +ᵣ x' , u)) -ᵣ fst (g (y , fPos (fst x) (snd x)))

   h≡Δg : h ≡ Δg
   h≡Δg = cong₂ _-ᵣ_ refl (cong fst (sym (retEq e x)))

   Δg/x'>0 : 0 <ᵣ Δg ·ᵣ invx'
   Δg/x'>0 =
     incr→0<differenceAtℙ pred0< (λ r 0<r → fst (g (r , 0<r)))
       y x' v (fPos (fst x) (snd x)) u
       λ _ _ _ _ → incrG _ _

   p0 : fst (invℝ₊ (Δ ·ᵣ invh , uuu)) ≡ fst (invℝ₊ (Δ₊ ₊·ᵣ invh₊))
   p0 =
     cong {x = Δ ·ᵣ invh , uuu} (fst ∘ invℝ₊)
       (ℝ₊≡ (sym (absᵣPos (Δ ·ᵣ invh) uuu) ∙ ·absᵣ Δ invh))

   p1 : fst (invℝ₊ (Δ₊ ₊·ᵣ invh₊)) ≡ fst (invℝ₊ Δ₊) ·ᵣ fst (invℝ₊ invh₊)
   p1 = cong fst (invℝ₊· Δ₊ invh₊)

   p2 : fst (invℝ₊ Δ₊) ≡ absᵣ invx'
   p2 =
     cong (fst ∘ invℝ₊) (ℝ₊≡ (cong absᵣ zzz))
       ∙ sym (absᵣ-invℝ x' v)

   p3 : fst (invℝ₊ invh₊) ≡ absᵣ Δg
   p3 =
     sym (absᵣ-invℝ invh (invℝ0＃ h h＃))
       ∙ cong absᵣ (invℝInvol h h＃ ∙ h≡Δg)

   p4 : absᵣ invx' ·ᵣ absᵣ Δg ≡ Δg ·ᵣ invx'
   p4 =
     ·ᵣComm _ _ ∙ sym (·absᵣ Δg invx') ∙ absᵣPos (Δg ·ᵣ invx') Δg/x'>0

-- Previous location: ExponentiationDer.invDerivativeℙ.
invDerivativeℙ : ∀ x (f : ℝ → ℝ) f' f'Pos (fPos : ∀ x → 0 <ᵣ f x)
  → (isEquivF : isEquiv {A = ℝ} {B = ℝ₊} λ x → f x  , fPos x)
   → (∀ x y → fst x <ᵣ fst y →
       (invEq (_ , isEquivF) x) <ᵣ (invEq (_ , isEquivF) y))
   → (∀ x y → x <ᵣ y →  (f x) <ᵣ (f y)) → IsContinuous f
  → IsContinuousWithPred pred0< (λ x x∈ → (invEq (_ , isEquivF) (x , x∈)))
  → derivativeOf f at x is f'
  → derivativeOfℙ pred0< , (λ r 0<r →
        (invEq (_ , isEquivF) (r , 0<r)))
         at f x , fPos _
       is fst (invℝ₊ (f' , f'Pos))
invDerivativeℙ x f f' f'Pos fPos isEquivF incrG incrF  fC gC dF =
 invDerivativeℙPos-temp
   (x , tt)
   (λ x _ → f x)
   f'
   f'Pos
   (λ v _ → fPos v)
   (snd (isoToEquiv rUnit×Iso ∙ₑ (_ , isEquivF)))
   (λ x₁ y x₂ → incrG _ _ x₂)
   (λ x₁ y x₂ → incrF _ _ x₂)
   (AsContinuousWithPred _ _ fC)
   gC
   (as-derivativeOfℙ _ _ _ _ _ dF)
-}
