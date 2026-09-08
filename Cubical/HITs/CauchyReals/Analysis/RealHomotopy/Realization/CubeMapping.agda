module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubeMapping where

open import Cubical.Foundations.Prelude hiding (Cube)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Cubes.Base
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (false; true)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit using (Unit; tt; Unit*; tt*; isSetUnit*)
open import Cubical.Data.Sigma
open import Cubical.HITs.Interval.Base using ()
  renaming (Interval to 𝕁; zero to zero𝕁; one to one𝕁; seg to seg𝕁)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.PushoutProduct using (PushProd; _×̂_)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareBoundary
  using (endpoints)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubicalShapes
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CylinderBoundary

private
  -- Keeping the whole restriction arrow in the inductive invariant
  -- retains boundary compatibility when taking the successor.
  Arrow : (ℓ : Level) → Type (ℓ-suc ℓ)
  Arrow ℓ = Σ[ C ∈ Type ℓ ] Σ[ B ∈ Type ℓ ] (C → B)

  PathObject : ∀ {ℓ} → Type ℓ → Type ℓ
  PathObject C = Σ[ x ∈ C ] Σ[ y ∈ C ] x ≡ y

  BoundaryObject : ∀ {ℓ} {C B : Type ℓ} → (C → B) → Type ℓ
  BoundaryObject {C = C} r = Σ[ x ∈ C ] Σ[ y ∈ C ] r x ≡ r y

  successor : ∀ {ℓ} → Arrow ℓ → Arrow ℓ
  successor (C , B , r) = PathObject C , BoundaryObject r ,
    λ (x , y , p) → x , y , cong r p

  arrowIsoPath : ∀ {ℓ} {C B C' B' : Type ℓ}
    (r : C → B) (s : C' → B') (eC : Iso C C') (eB : Iso B B') →
    ((x : C) → Iso.fun eB (r x) ≡ s (Iso.fun eC x)) →
    Path (Arrow ℓ) (C , B , r) (C' , B' , s)
  arrowIsoPath r s eC eB square i =
    ua (isoToEquiv eC) i , ua (isoToEquiv eB) i , λ x →
      ua-glue (isoToEquiv eB) i (λ { (i = i0) → r x })
        (inS (hcomp (λ j → λ
          { (i = i0) → square x (~ j)
          ; (i = i1) → s x })
          (s (ua-unglue (isoToEquiv eC) i x))))

  module _ {ℓ} {A : Type ℓ} {D : Type} where
    intervalMap : PathObject (D → A) → (𝕁 × D → A)
    intervalMap (f , g , p) (zero𝕁 , d) = f d
    intervalMap (f , g , p) (one𝕁 , d) = g d
    intervalMap (f , g , p) (seg𝕁 i , d) = p i d

    intervalMapsIso : Iso (PathObject (D → A)) (𝕁 × D → A)
    Iso.fun intervalMapsIso = intervalMap
    Iso.inv intervalMapsIso f =
      (λ d → f (zero𝕁 , d)) , (λ d → f (one𝕁 , d)) , λ i d → f (seg𝕁 i , d)
    Iso.sec intervalMapsIso f i (zero𝕁 , d) = f (zero𝕁 , d)
    Iso.sec intervalMapsIso f i (one𝕁 , d) = f (one𝕁 , d)
    Iso.sec intervalMapsIso f i (seg𝕁 j , d) = f (seg𝕁 j , d)
    Iso.ret intervalMapsIso _ = refl

  module _ {ℓ} {A : Type ℓ} {B D : Type} (b : B → D) where
    restriction : (D → A) → (B → A)
    restriction f y = f (b y)

    pushoutMap : BoundaryObject restriction → (Pushout b b → A)
    pushoutMap (f , g , p) (inl d) = f d
    pushoutMap (f , g , p) (inr d) = g d
    pushoutMap (f , g , p) (push y i) = p i y

    pushoutMapsIso : Iso (BoundaryObject restriction) (Pushout b b → A)
    Iso.fun pushoutMapsIso = pushoutMap
    Iso.inv pushoutMapsIso f =
      (λ d → f (inl d)) , (λ d → f (inr d)) , λ i y → f (push y i)
    Iso.sec pushoutMapsIso f i (inl d) = f (inl d)
    Iso.sec pushoutMapsIso f i (inr d) = f (inr d)
    Iso.sec pushoutMapsIso f i (push y j) = f (push y j)
    Iso.ret pushoutMapsIso _ = refl

    boundaryMapsSuccessorIso :
      Iso (BoundaryObject restriction) (PushProd endpoints b → A)
    boundaryMapsSuccessorIso = compIso pushoutMapsIso
      (domIso (invIso (cylinderBoundaryIso b)))

    successor-square : (c : PathObject (D → A)) →
      Iso.fun boundaryMapsSuccessorIso (snd (snd (successor (_ , _ , restriction))) c) ≡
      (λ z → intervalMap c ((endpoints ×̂ b) z))
    successor-square c i (inl (false , d)) = fst c d
    successor-square c i (inl (true , d)) = fst (snd c) d
    successor-square c i (inr (zero𝕁 , y)) = fst c (b y)
    successor-square c i (inr (one𝕁 , y)) = fst (snd c) (b y)
    successor-square c i (inr (seg𝕁 j , y)) = snd (snd c) j (b y)
    successor-square c i (push (false , y) j) = fst c (b y)
    successor-square c i (push (true , y) j) = fst (snd c) (b y)

    geometricSuccessor :
      successor (_ , _ , restriction) ≡
      ((𝕁 × D → A) , (PushProd endpoints b → A) ,
        (λ f z → f ((endpoints ×̂ b) z)))
    geometricSuccessor = arrowIsoPath _ _ intervalMapsIso
      boundaryMapsSuccessorIso successor-square

module _ {ℓ} (A : Type ℓ) where
  private
    geometricArrow : ℕ → Arrow ℓ
    geometricArrow n = (CubeDisk n → A) , (CubeBoundary n → A) ,
      restriction (cubeBoundaryMap n)

    internalArrow : ℕ → Arrow ℓ
    internalArrow n = Cube n A , ∂Cube n A , ∂_ {n = n}

    internalDiskIso : (n : ℕ) → Iso (PathObject (Cube n A)) (Cube (suc n) A)
    Iso.fun (internalDiskIso zero) (x , y , p) = (x , y) , p
    Iso.inv (internalDiskIso zero) ((x , y) , p) = x , y , p
    Iso.sec (internalDiskIso zero) _ = refl
    Iso.ret (internalDiskIso zero) _ = refl
    Iso.fun (internalDiskIso (suc n)) (x , y , p) =
      (x , y , (λ i → fst (p i))) , λ i → snd (p i)
    Iso.inv (internalDiskIso (suc n)) ((x , y , p) , q) =
      x , y , λ i → p i , q i
    Iso.sec (internalDiskIso (suc n)) _ = refl
    Iso.ret (internalDiskIso (suc n)) _ = refl

    internalBoundaryIso : (n : ℕ) →
      Iso (BoundaryObject (∂_ {n = n} {A = A})) (∂Cube (suc n) A)
    Iso.fun (internalBoundaryIso zero) (x , y , p) = x , y
    Iso.inv (internalBoundaryIso zero) (x , y) = x , y , refl
    Iso.sec (internalBoundaryIso zero) _ = refl
    Iso.ret (internalBoundaryIso zero) (x , y , p) i =
      x , y , isSetUnit* tt* tt* refl p i
    internalBoundaryIso (suc n) = idIso

    internal-square : (n : ℕ) (c : PathObject (Cube n A)) →
      Iso.fun (internalBoundaryIso n) (snd (snd (successor (internalArrow n))) c) ≡
      ∂ (Iso.fun (internalDiskIso n) c)
    internal-square zero c = refl
    internal-square (suc n) c = refl

    internalSuccessor : (n : ℕ) → successor (internalArrow n) ≡ internalArrow (suc n)
    internalSuccessor n = arrowIsoPath _ _ (internalDiskIso n)
      (internalBoundaryIso n) (internal-square n)

    unitMapsIso : Iso (Unit → A) A
    Iso.fun unitMapsIso f = f tt
    Iso.inv unitMapsIso a _ = a
    Iso.sec unitMapsIso a = refl
    Iso.ret unitMapsIso f i tt = f tt

    emptyMapsIso : Iso (⊥ → A) (Unit* {ℓ})
    Iso.fun emptyMapsIso _ = tt*
    Iso.inv emptyMapsIso _ ()
    Iso.sec emptyMapsIso tt* = refl
    Iso.ret emptyMapsIso f i ()

    -- The same successor acts on both arrows. Congruence carries the
    -- entire induction hypothesis, including its restriction square.
    mappingArrows : (n : ℕ) → geometricArrow n ≡ internalArrow n
    mappingArrows zero = arrowIsoPath _ _ unitMapsIso emptyMapsIso (λ _ → refl)
    mappingArrows (suc n) =
      sym (geometricSuccessor (cubeBoundaryMap n))
      ∙ cong successor (mappingArrows n)
      ∙ internalSuccessor n

  diskMapsEquiv : (n : ℕ) → (CubeDisk n → A) ≃ Cube n A
  diskMapsEquiv n = pathToEquiv (λ i → fst (mappingArrows n i))

  boundaryMapsEquiv : (n : ℕ) → (CubeBoundary n → A) ≃ ∂Cube n A
  boundaryMapsEquiv n = pathToEquiv (λ i → fst (snd (mappingArrows n i)))

  restriction-compatibility : (n : ℕ) (f : CubeDisk n → A) →
    fst (boundaryMapsEquiv n) (λ z → f (cubeBoundaryMap n z)) ≡
    ∂ (fst (diskMapsEquiv n) f)
  restriction-compatibility n f = fromPathP λ i →
    snd (snd (mappingArrows n i))
      (transport-filler (λ j → fst (mappingArrows n j)) f i)

  private
    internalFiberIso : (n : ℕ) (b : ∂Cube n A) →
      Iso (fiber (∂_ {n = n} {A = A}) b) (CubeRel n A b)
    Iso.fun (internalFiberIso zero tt*) = fst
    Iso.inv (internalFiberIso zero tt*) a = a , refl
    Iso.sec (internalFiberIso zero tt*) a = refl
    Iso.ret (internalFiberIso zero tt*) (a , p) i =
      a , isSetUnit* tt* tt* refl p i
    internalFiberIso (suc n) b =
      invIso (fiberProjIso (∂Cube (suc n) A) (CubeRel (suc n) A) b)

  -- A disk map with a specified boundary agreement is precisely a
  -- relative cube, for every n and every higher target A.
  cubeExtensionEquiv : (n : ℕ) (b : CubeBoundary n → A) →
    fiber (λ (f : CubeDisk n → A) z → f (cubeBoundaryMap n z)) b ≃
    CubeRel n A (fst (boundaryMapsEquiv n) b)
  cubeExtensionEquiv n b = compEquiv
    (pathToEquiv (λ i → fiber (snd (snd (mappingArrows n i)))
      (transport-filler (λ j → fst (snd (mappingArrows n j))) b i)))
    (isoToEquiv (internalFiberIso n (fst (boundaryMapsEquiv n) b)))
