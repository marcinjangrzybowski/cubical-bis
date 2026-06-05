module Cubical.Tactics.CommRingSolver.OrderedSolver.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.FinData renaming (punchOut to punchOut')
open import Cubical.Data.Nat using (ℕ;suc;zero)
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ using (zero-≤)
open import Cubical.Data.Vec as Vec
open import Cubical.Data.Sigma
import Cubical.Data.Prod as ×
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.NatPlusOne
open import Cubical.Data.List as L hiding (drop)
open import Cubical.Data.List.Dependent
open import Cubical.Data.Bool as 𝟚 hiding (_≟_)
open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Unit
open import Cubical.Data.Sum as ⊎
open import Cubical.Relation.Nullary

open import Cubical.Reflection.Sugar
open import Agda.Builtin.Reflection hiding (Type)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Properties as OCR
open import Cubical.Algebra.Ring
open import Cubical.Tactics.CommRingSolver.RawAlgebra hiding (⟨_⟩)
open import Cubical.Tactics.CommRingSolver.AlgebraExpression
open import Cubical.Tactics.CommRingSolver.HornerForms
open import Cubical.Tactics.CommRingSolver.RawRing hiding (⟨_⟩)
open import Cubical.Tactics.CommRingSolver.EvalHom
open import Cubical.Tactics.CommRingSolver.OrderedConfig
open import Cubical.Algebra.Ring.BigOps

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Tactics.Reflection.Error
open import Agda.Builtin.String
 
open import Cubical.Tactics.CommRingSolver.Solver.Core as Solver


data NoInfo : Type where
 noInfoMsg : String → NoInfo
 noVarInfo : ℕ → NoInfo

UseAssumptionFailReason = List ErrorPart

data FailReason : Type where
 tooWeak : String → FailReason
 missingInfo : List NoInfo → FailReason
 unableToUseAssumption : UseAssumptionFailReason → FailReason


module _ {ℓ` oℓ`} (R` : CommRing ℓ`) (O`@((_<`_ , _≤`_) , _) : RingOrdering oℓ` R`) where
 private
  OR` = Iso.inv IsoΣRingOrdering (R` , O`)

  open CommRingStr (snd R`) using () renaming
    (0r to 0r`;1r to 1r`;_+_ to _+`_; _·_ to _·`_; -_ to -`_ ; _-_ to _-`_)

  module OCR` where
   open IsOrderedCommRing (snd O`) public
   open OrderedCommRingTheory OR` public

  module R` where
    open CommRingStr (snd R`) public
    open RingTheory (CommRing→Ring R`) public
    open CommRingTheory R` public

  open OCR` using () renaming (_#_ to _#`_)

  module RT` = RingTheory (CommRing→Ring R`)
 module AnnotatedRing (mb·`lCancel : Maybe (∀ c m n → c ·` m ≡ c ·` n → (c ≡ 0r` → ⊥) → m ≡ n)) where
   
  data IneqInfo (x : ⟨ R` ⟩) : Type (ℓ-max ℓ` oℓ`) where
   noInfo : List NoInfo → IneqInfo x
   isPositive : (0r` <` x)  → IneqInfo x
   isNonNeg : (0r` ≤` x) → IneqInfo x
   isNonZero : (x #` 0r`) → IneqInfo x
   isZero : (x ≡ 0r`) → IneqInfo x

  noInfo' : ∀ {x} → String → IneqInfo x
  noInfo' s = noInfo [ noInfoMsg s ]
  
  _ii∧_ : ∀ {x} → IneqInfo x → IneqInfo x → IneqInfo x 
  (noInfo _) ii∧ x = x
  x ii∧ (noInfo _) = x
  isPositive x ii∧ _ = isPositive x
  _ ii∧ isPositive x = isPositive x
  (isNonZero (inr x)) ii∧ _ = isPositive x
  _ ii∧ (isNonZero (inr x)) = isPositive x
  (isNonNeg x) ii∧ _ = isNonNeg x
  _ ii∧ (isNonNeg x) = isNonNeg x
  (isNonZero (inl x)) ii∧ _ = (isNonZero (inl x))
  _ ii∧ (isNonZero (inl x)) = (isNonZero (inl x))
  isZero x ii∧ _ = isZero x
  
  _ii+_ : ∀ {x y} → IneqInfo x → IneqInfo y → IneqInfo (x +` y)
  isZero x ii+ x₁ = subst IneqInfo (sym (RT`.+IdL' _ _ x)) x₁
  x ii+ isZero x₁ = subst IneqInfo (sym (RT`.+IdR' _ _ x₁)) x
  (noInfo s) ii+ (noInfo s') = noInfo (s L.++ s')
  (noInfo s) ii+ x₁ = (noInfo s)
  x₁ ii+ (noInfo s) = (noInfo s)
  isNonZero x ii+ x₁ = (noInfo' "nonZero+smth")
  x ii+ isNonZero x₁ = (noInfo' "smth+nonZero")
  isPositive x ii+ isPositive x₁ = isPositive (subst (_<` _) (R`.+IdL _) (OCR`.+Mono< _ _ _ _ x x₁))
  isPositive x ii+ isNonNeg x₁ =
    isPositive (OCR`.<-≤-trans _ _ _ x (OCR`.≤SumLeftNonNeg _ _ x₁))
  isNonNeg x ii+ isPositive x₁ =
    isPositive (OCR`.<-≤-trans _ _ _ x₁ (OCR`.≤SumRightNonNeg _ _ x))
  isNonNeg x ii+ isNonNeg x₁ =
   isNonNeg
    ( (subst (_≤` _) (R`.+IdL _) (OCR`.+Mono≤ _ _ _ _ x x₁)))

  0#x·y : ∀ {x y} → (x #` 0r`) → (y #` 0r`) → IneqInfo (x ·` y)
  0#x·y (inl x) (inl x₁) = isPositive ((subst2 (_<`_)
   (RT`.0RightAnnihilates _) 
   (RT`.-Dist· _ _)
   (OCR`.·MonoL< _ _ _ (OCR`.<0→0<- _ x) (OCR`.<0→0<- _ x₁))))
  0#x·y (inl x) (inr x₁) = isNonZero
   (inl (subst (_ <`_) (RT`.0LeftAnnihilates _) (OCR`.·MonoR< _ _ _ x₁ x)))
  0#x·y (inr x) (inl x₁) = isNonZero
   (inl (subst (_ <`_) (RT`.0RightAnnihilates _) (OCR`.·MonoL< _ _ _ x x₁)))
  0#x·y (inr x) (inr x₁) = isPositive
   (subst (_<` _) (RT`.0RightAnnihilates _) (OCR`.·MonoL< _ _ _ x x₁))

  _ii·_ : ∀ {x y} → IneqInfo x → IneqInfo y → IneqInfo (x ·` y)
  isZero x ii· y = isZero (RT`.0LeftAnnihilates' _ _ x)
  x ii· isZero y = isZero (RT`.0RightAnnihilates' _ _ y)
  (noInfo s) ii· (noInfo s') = noInfo (s L.++ s')
  (noInfo s) ii· x₁ = noInfo s
  x₁ ii· (noInfo s) = (noInfo s)
  isPositive x ii· isPositive x₁ = isPositive
    (subst (_<` _) (RT`.0RightAnnihilates _) (OCR`.·MonoL< _ _ _ x x₁))
  isPositive x ii· isNonNeg x₁ = isNonNeg
    (subst (_≤` _) (RT`.0RightAnnihilates _) (OCR`.·MonoL≤ _ _ _ (OCR`.<-≤-weaken _ _ x) x₁))
  isPositive x ii· isNonZero x₁ =
    (0#x·y (inr x) x₁)  
  isNonNeg x ii· isPositive x₁ = isNonNeg
    (subst (_≤` _) (RT`.0RightAnnihilates _) (OCR`.·MonoL≤ _ _ _ x (OCR`.<-≤-weaken _ _ x₁)))
  isNonNeg x ii· isNonNeg x₁ = isNonNeg
   (subst (_≤` _) (RT`.0RightAnnihilates _) (OCR`.·MonoL≤ _ _ _ x x₁) )
  isNonNeg x ii· isNonZero (inl x₁) = noInfo' "isNonNeg·Neg" 
  isNonNeg x ii· isNonZero (inr x₁) = isNonNeg
    (subst (_≤` _) (RT`.0RightAnnihilates _) (OCR`.·MonoL≤ _ _ _ x (OCR`.<-≤-weaken _ _ x₁)))
  isNonZero x ii· isPositive x₁ =
    0#x·y x (inr x₁) 
  isNonZero (inl x) ii· isNonNeg x₁ = noInfo' "Neg·isNonNeg"
  isNonZero (inr x) ii· isNonNeg x₁ = isNonNeg
    (subst (_≤` _) (RT`.0RightAnnihilates _) (OCR`.·MonoL≤ _ _ _ (OCR`.<-≤-weaken _ _ x) x₁))
  isNonZero x ii· isNonZero x₁ = 0#x·y x x₁

  ii-_ : ∀ {x} → IneqInfo x → IneqInfo (-` x)
  ii- (noInfo s) = noInfo (noInfoMsg "todo ii-_" L.∷ s)
  ii- x = (noInfo' "todo ii-_")

  Σ≡₁ : ∀ {x y a a'} → x ≡ y → Path (Σ[ x ∈ ⟨ R` ⟩ ] ∥ IneqInfo x ∥₁) (x , a) (y , a')
  Σ≡₁ = Σ≡Prop (λ _ → squash₁)

  R`A : CommRing (ℓ-max ℓ` oℓ`) 
  R`A .fst = Σ[ x ∈ ⟨ R` ⟩ ] ∥ IneqInfo x ∥₁
  R`A .snd .CommRingStr.0r = 0r` , ∣ isZero refl ∣₁
  R`A .snd .CommRingStr.1r = 1r` , ∣ isPositive OCR`.0<1 ∣₁
  R`A .snd .CommRingStr._+_ (_ , x) (_ , y)  = _ , PT.map2 _ii+_ x y
  R`A .snd .CommRingStr._·_ (_ , x) (_ , y)  = _ , PT.map2 _ii·_ x y
  (CommRingStr.- R`A .snd)  (_ , x) = _ , PT.map (ii-_) x
  R`A .snd .CommRingStr.isCommRing .IsCommRing.isRing =
   makeIsRing
     (isSetΣ R`.is-set λ _ → isProp→isSet squash₁)
     (λ _ _ _ → Σ≡₁ (R`.+Assoc _ _ _ ))
     (λ _ → Σ≡₁ (R`.+IdR _ ))
     (λ _ → Σ≡₁ (R`.+InvR _ ))
     (λ _ _ → Σ≡₁ (R`.+Comm _ _ ))
     (λ _ _ _ → Σ≡₁ (R`.·Assoc _ _ _ ))
     (λ _ → Σ≡₁ (R`.·IdR _ ))
     (λ _ → Σ≡₁ (R`.·IdL _ ))
     (λ _ _ _ → Σ≡₁ (R`.·DistR+ _ _ _ ))
     (λ _ _ _ → Σ≡₁ (R`.·DistL+ _ _ _ ))
  R`A .snd .CommRingStr.isCommRing .IsCommRing.·Comm _ _ = Σ≡₁ (R`.·Comm _ _ )


module SansReflectionOrdered (ocrs : OrderedCommRingSolverConfig) where

 open OrderedCommRingSolverConfig ocrs
 open Solver.SansReflection commRingSolverConfig  
 
 private
  module RT` = RingTheory (CommRing→Ring R`)

 _≲[_]_ : ⟨ R` ⟩ → Bool → ⟨ R` ⟩ → Type oℓ`  
 x ≲[ false ] y = x ≤` y
 x ≲[ true ] y = x <` y



 from≲T : ∀ x y b → x <` y → (x ≲[ b ] y)
 from≲T x y false x₁ = OCR`.<-≤-weaken _ _ x₁
 from≲T x y true x₁ = x₁
 
 open AnnotatedRing R` (_ , iocr`) mb·`lCancel public

 
 
 
 
 IneqInfo→Mb≲ : ∀ x b → IneqInfo x → (FailReason) ⊎ (0r` ≲[ b ] x)
 IneqInfo→Mb≲ x b (noInfo x₁) = inl (missingInfo x₁)
 IneqInfo→Mb≲ x b (isPositive x₁) = inr (from≲T _ _ b x₁)
 IneqInfo→Mb≲ x false (isNonNeg x₁) = inr x₁
 IneqInfo→Mb≲ x true (isNonNeg x₁) = inl (tooWeak "nonNeg - to weak to prove <")
 IneqInfo→Mb≲ x b (isNonZero x₁) = inl (tooWeak "nonZero - to weak to prove either ≤ or <")
 IneqInfo→Mb≲ x false (isZero x₁) = inr (subst (0r` ≤`_) (sym x₁) (OCR`.is-refl 0r`))
 IneqInfo→Mb≲ x true (isZero x₁) = inl (tooWeak "not true - is zero")
 
 0≲y-x→x≲y : ∀ b x y → 0r` ≲[ b ] (y -` x) → x ≲[ b ] y 
 0≲y-x→x≲y false = OCR`.0≤Δ→≤
 0≲y-x→x≲y true = OCR`.0<Δ→<

 x≲y→0≲y-x : ∀ b x y → x ≲[ b ] y → 0r` ≲[ b ] (y -` x) 
 x≲y→0≲y-x false = OCR`.≤→0≤Δ
 x≲y→0≲y-x true = OCR`.<→0<Δ




 VarsIneqInfo : (n : ℕ) (xs : Vec ⟨ R` ⟩ n) → Type (ℓ-max ℓ` oℓ`)
 VarsIneqInfo n [] = Unit*
 VarsIneqInfo (suc n) (x ∷ po) = IneqInfo x × VarsIneqInfo n po

 partitionVarsByHavingInfo : ∀ {n} {xs} → VarsIneqInfo n xs → (List (Fin n) × List (Fin n))
 partitionVarsByHavingInfo {xs = []} _ = [] , []
 partitionVarsByHavingInfo {xs = _ ∷ xs} (AnnotatedRing.noInfo x , z) =
   map-× ((zero ∷_) ∘ L.map suc) (L.map suc) (partitionVarsByHavingInfo z)
 partitionVarsByHavingInfo {xs = _ ∷ xs} (_ , z) =
  map-× (L.map suc) ((zero ∷_) ∘ L.map suc) (partitionVarsByHavingInfo z)
  
 dropVarsIneqInfo : ∀ {n} {xs} k → VarsIneqInfo (suc n) xs → VarsIneqInfo n (drop k xs)  
 dropVarsIneqInfo {xs = x₁ ∷ xs} zero = snd
 dropVarsIneqInfo {suc n} {xs = x₁ ∷ xs} (suc k) = map-snd (dropVarsIneqInfo {n} {xs} k)


 
 module _ (n : ℕ) {ℓa} (A : ℕ → Type ℓa) {{eiv : EvalInVecR A}}  where
 
  record Inequality (xs : Vec ⟨ R` ⟩ n) : Type ℓa where
   constructor inequality
   field
    goalRel : Bool
    goalLHS goalRHS : A n

   InequalityTy : Type oℓ`
   InequalityTy = (evalInVecR goalLHS xs ≲[ goalRel ] evalInVecR goalRHS xs)


  open Inequality using (InequalityTy) public

   

  Assumption = λ (xs : Vec ⟨ R` ⟩ n)  →
     (Σ[ (b , e , _) ∈ (Bool × A n × Maybe (Fin n)) ] (0r` ≲[ b ] evalInVecR e xs))


  record Problem (m : ℕ) {ℓg} (goal : Type ℓg) : Type (ℓ-max (ℓ-max oℓ` ℓ) (ℓ-max ℓa (ℓ-max ℓ` ℓg))) where
   
   field
    xs : Vec ⟨ R` ⟩ n
    vii : VarsIneqInfo n xs
    assumptions : Vec (Assumption xs) m
    goalRel : Bool
    goalExpr : A n

   Solution : Type oℓ`
   Solution = 0r` ≲[ goalRel ] evalInVecR goalExpr xs
   field
    solution : Solution → goal

 Assumption' = λ (n : ℕ) (xs : Vec ⟨ R` ⟩ n) →
  Σ (Inequality n RExpr xs × Maybe (Fin n)) (InequalityTy ∘ fst)
    
 mkProblemRE : ∀ n xs → (l : List (Assumption' n xs))
           → VarsIneqInfo n xs
           → (b : Bool)
           → (lhse rhse : RExpr n) 
           → Problem n  RExpr (L.length l) (evalInVecR lhse xs ≲[ b ] evalInVecR rhse xs)
 mkProblemRE n xs _ _ _ _ _ .Problem.xs = xs
 mkProblemRE n xs l _ _ _ _ .Problem.assumptions =
   Vec.map (λ ((inequality b lhse rhse , k) , p) → (b , rhse +' -' lhse , k) ,
     x≲y→0≲y-x b (⟦ lhse ⟧ xs) (⟦ rhse ⟧ xs) p) (Vec.fromList l)
 mkProblemRE n xs _ einf _ _ _ .Problem.vii = einf
 mkProblemRE n xs _ _ b _ _ .Problem.goalRel = b
 mkProblemRE n xs _ _ _ lhse rhse .Problem.goalExpr = rhse +' -' lhse
 mkProblemRE n xs _ _ b lhse rhse .Problem.solution = 0≲y-x→x≲y b (⟦ lhse ⟧ xs)  (⟦ rhse ⟧ xs)


 Problem≑> : ∀ {ℓa ℓg} {ℓa'} {A : ℕ → Type ℓa} {{_ : EvalInVecR A}}
              {A' : ℕ → Type ℓa'} {{_ : EvalInVecR A'}} {G : Type ℓg}
          → (A ≑> A') → ∀ {n m}
           → Problem n A m G → Problem n A' m G
 Problem≑> (≑>-c to to~) x .Problem.xs = x .Problem.xs  
 Problem≑> (≑>-c to to~) x .Problem.assumptions =
   Vec.map (λ ((b , (e , k)) , p) → (b , (to e , k))
    , subst (0r` ≲[ b ]_) (to~ e _) p) (x .Problem.assumptions)
 Problem≑> (≑>-c to to∼) x .Problem.vii = x .Problem.vii
 Problem≑> (≑>-c to to∼) x .Problem.goalRel = x .Problem.goalRel
 Problem≑> (≑>-c to to∼) x .Problem.goalExpr = to (x .Problem.goalExpr)
 Problem≑> (≑>-c to to∼) x .Problem.solution =
   (x .Problem.solution) ∘
    subst (0r` ≲[ (x .Problem.goalRel) ]_) (sym (to∼ (x .Problem.goalExpr) (x .Problem.xs))) 
      
 setVarsIneqInfo : ∀ {n} (xs : Vec ⟨ R` ⟩ n) (k : Fin n)
        → IneqInfo (lookup k xs)
        → VarsIneqInfo n xs → VarsIneqInfo n xs
 setVarsIneqInfo (x₂ ∷ xs) zero x = map-fst (x ii∧_) 
 setVarsIneqInfo (x₂ ∷ xs) (suc k) x = map-snd (setVarsIneqInfo xs k x)

 setVarsIneqInfo' : ∀ (n) (xs : Vec ⟨ R` ⟩ n) (k : Fin n) b
        → 0r` ≲[ b ] lookup k xs
        → VarsIneqInfo n xs → VarsIneqInfo n xs
 setVarsIneqInfo' _ xs k false u = setVarsIneqInfo xs k (isNonNeg u)
 setVarsIneqInfo' _ xs k true u = setVarsIneqInfo xs k (isPositive u)

 updVarsIneqInfo : ∀ {n} f (xs : Vec ⟨ R` ⟩ n) (k : Fin n)
        → IneqInfo (f (lookup k xs))
        → VarsIneqInfo n xs → VarsIneqInfo n (update k f xs)
 updVarsIneqInfo f (x₂ ∷ xs) zero x = map-fst (λ _ → x) 
 updVarsIneqInfo f (x₂ ∷ xs) (suc k) x = map-snd (updVarsIneqInfo f xs k x)

 ≲→IneqInfo : ∀ b {x} → 0r` ≲[ b ] x → IneqInfo x
 ≲→IneqInfo false {x} = isNonNeg
 ≲→IneqInfo true {x} = isPositive
 
 updVarsIneqInfo' : ∀ (n) f (xs : Vec ⟨ R` ⟩ n) (k : Fin n) b
        → 0r` ≲[ b ] (f (lookup k xs))
        → VarsIneqInfo n xs → VarsIneqInfo n (update k f xs)
 updVarsIneqInfo' _ f xs k b u = updVarsIneqInfo f xs k (≲→IneqInfo b u)



 varsIneqNoInfo' : (k n : ℕ) (xs : Vec ⟨ R` ⟩ n) → VarsIneqInfo n xs 
 varsIneqNoInfo' _ _ [] = tt*
 varsIneqNoInfo' k _ (x ∷ xs) = noInfo [ noVarInfo k ] , (varsIneqNoInfo' (suc k) _ xs)

 varsIneqNoInfo : (n : ℕ) (xs : Vec ⟨ R` ⟩ n) → VarsIneqInfo n xs 
 varsIneqNoInfo = varsIneqNoInfo' zero

 ²IneqInfo : ∀ v → IneqInfo v → IneqInfo (v ·` v)
 ²IneqInfo v (noInfo x) = isNonNeg (OCR`.0≤² v)
 ²IneqInfo v (isPositive x) = isPositive (subst (_<` _)
   (R`.0RightAnnihilates _) (OCR`.·MonoL< _ _ _ x x))
 ²IneqInfo v (isNonNeg x) = isNonNeg (OCR`.0≤² v)
 ²IneqInfo v (isNonZero x) = isPositive (OCR`.#→0<² _ x)
 ²IneqInfo v (isZero x) = isZero (RT`.0LeftAnnihilates' _ _ x)
 
 ^IneqInfo : ∀ v → IneqInfo v → ∀ m → IneqInfo (fromJust-def 1r` (v powMaybe m))
 ^IneqInfo v _ zero = isPositive OCR`.0<1
 ^IneqInfo v y one = y
 ^IneqInfo v y (suc (suc m)) =
   subst IneqInfo (sym (R`.·Assoc _ _ _))
     (²IneqInfo v y ii· subst IneqInfo (powMaybe≡^ v m) (^IneqInfo v y m))

 scalarIneqInfo : ∀ a → IneqInfo (fromJust-def 1r` (map-Maybe scalar` a))
 scalarIneqInfo nothing = isPositive OCR`.0<1
 scalarIneqInfo (just x) =
   decRec (isPositive ∘S subst (_<` (scalar` x)) pres0 ∘S pres< _ _)
    (λ _ →
      decRec (isNonNeg ∘S subst (_≤` (scalar` x)) pres0 ∘S pres≤ _ _)
      (λ _ → noInfo' "todo negative scalar") (0r ≤? x))
    (0r <? x)
 
 monomialIneqInfo : ∀ n m xs → VarsIneqInfo n xs → IneqInfo (Mb.fromJust-def 1r` (evalMonomial m xs))
 monomialIneqInfo n [] xs x = isPositive OCR`.0<1
 monomialIneqInfo .one (_∷_ {zero} m xs) (v ∷ vs) x = ^IneqInfo v (x .fst) m
 monomialIneqInfo .(suc (suc n)) (_∷_ {suc n} m xs) (v ∷ vs) x =
   subst IneqInfo
  (sym (fromJust-def-mb·`mb (evalMonomial xs vs)  (v powMaybe m)))
    (monomialIneqInfo _ xs vs (snd x) ii· ^IneqInfo v (x .fst) m)
    
 polyTermIneqInfo : ∀ n pt xs → VarsIneqInfo n xs → IneqInfo (evalPolynomialTerm {n} pt xs)
 polyTermIneqInfo n (false , a , b) xs x =
   noInfo (noInfoMsg "todo false in polyTerm : " ∷ [ noInfoMsg $ caseMaybe "n" "j" a ] )
 polyTermIneqInfo n (true , a , b) xs x =
  subst IneqInfo (sym (fromJust-def-mb·`mb (map-Maybe (fst (snd commAlg)) a) _))
    (scalarIneqInfo a ii· monomialIneqInfo n b xs x)
 
 polyIneqInfo : ∀ n po xs → VarsIneqInfo n xs → IneqInfo (evalPolynomial {n} po xs)
 polyIneqInfo n [] xs _ = isZero refl
 polyIneqInfo n (x ∷ po) xs y =
   let u = polyIneqInfo n po xs y ii+ polyTermIneqInfo n x xs y
   in subst IneqInfo (sym (evalPolynomial∷ x po xs)) u

 polyIneqInfoFromNoInfo : ∀ n po xs  → IneqInfo (evalPolynomial {n} po xs)
 polyIneqInfoFromNoInfo n po xs = polyIneqInfo n po xs (varsIneqNoInfo n xs)


 module Decidable≲ {requireDiscreteScalar : IsJust mbDiscreteScalars} where
  open Decidable {requireDiscreteScalar}
  x≲y-fromDecΣ : ∀ (n : ℕ) b (e₀ e₁ : RExpr n) (xs : Vec (fst R`) n) →
        Σ[ po ∈ _ ] (0r` ≲[ b ] evalPolynomial po xs → (⟦ e₀ ⟧ xs) ≲[ b ] (⟦ e₁ ⟧ xs))
       
  x≲y-fromDecΣ n b e₀ e₁ xs =
   let e = (e₁ +' -' e₀)
       ne , q = normalizeIHF (normalize e)
       po , p = Horner→Poly ne
       
   in po , 0≲y-x→x≲y b _ _ ∘S subst (0r` ≲[ b ]_) (p xs ∙ sym (q xs) ∙ isEqualToNormalform e xs)

  x≲y-fromDec : ∀ (n : ℕ) b (e₀ e₁ : RExpr n) (xs : Vec (fst R`) n) →
         (0r` ≲[ b ] _ → (⟦ e₀ ⟧ xs) ≲[ b ] (⟦ e₁ ⟧ xs))
       
  x≲y-fromDec n b e₀ e₁ xs = snd (x≲y-fromDecΣ n b e₀ e₁ xs)




  mbSimpleElim : ∀ n (P : IteratedHornerForms (suc n)) k xs
    → 0r` ≡ eval P xs
    → Elimination P k 1
    → Maybe (Σ[ (a , Q) ∈ (Σ (R .fst) (0r <_) × IteratedHornerForms n) ]
     ((scalar` (fst a) ·` (lookup k xs)) ≡ evalInVecR Q (drop k xs)))
  mbSimpleElim n P k xs 0=P E = do
    s , s≠0 , S=s ← IsConst? _ S
    let u = cong₂ _·`_ (sym (S=s _)) (sym (R`.·IdR _))
             ∙  (R‵.implicitInverse _ _ (R`.+Comm _ _ ∙ S·xᵏ+Q≡P xs ∙ sym 0=P))
    just
      (⊎.rec (⊥.rec ∘ s≠0)
        (⊎.rec
           (λ s<0 → (((- s) , (OCR.<0→0<- s s<0)) , Q) ,
               (cong₂ _·`_ (pres- s) refl ∙  R`.-DistL· _ _ ∙∙ cong -`_ u ∙∙ R`.-Idempotent _ ))
           (λ 0<s → ((s , 0<s) , -ₕ Q) , u ∙ (sym (-EvalDist Q (drop k xs)))))
        (≡<>? s 0r))

   where
   open Elimination E
    
  mbVerySimpleElim : ∀ n (P : IteratedHornerForms (suc n)) k xs 
    → 0r` ≡ eval P xs
    → Elimination P k 1
    → Maybe (Σ[ Q ∈ IteratedHornerForms n ]
     (
       ((lookup k xs)) ≡ evalInVecR Q (drop k xs)))
  mbVerySimpleElim n P k xs 0=P E = do
     se@(((s , 0<s) , Q) , p) ← mbSimpleElim n P k xs 0=P E
     decRec
      (λ s=1 → pure (Q , sym (R`.·IdL' _ _ (cong scalar` s=1 ∙ pres1)) ∙  p))
      (λ _ → do
        (1/s , s·1/s=1) ← mbInverses <* s <* 0<s
        let (Q' , Q'=) = const·ₕ 1/s Q
        pure (Q' , ((sym (R`.·IdL' _ _ (R`.·Comm _ _ ∙
                (sym (pres· _ _) ∙∙ cong scalar` s·1/s=1 ∙∙ pres1))) ∙ (sym $ R`.·Assoc _ _ _))
          ∙∙ cong (scalar` 1/s ·`_) p
          ∙∙ sym (Q'= (drop k xs)))))
       (s ≟ 1r)
    

  ElimData : ∀ {n m ℓg G} → Problem (suc n) IteratedHornerForms (suc m) {ℓg} G →
     Fin (suc m) → Type (ℓ-max (ℓ-max ℓ ℓ`) oℓ`)
  ElimData {n} {m} PRB assId = 
              Σ[ (k , P , (q , ≲q)) ∈ Fin (suc n) ×
                      IteratedHornerForms (suc n) ×
                      (Σ[ yy ∈ ⟨ R` ⟩ ] (0r` ≲[ fst (fst (lookup assId P.assumptions)) ] yy)) ]
                      (lookup k P.xs ≡ eval P (q ∷ drop k P.xs))
    where module P = Problem PRB
  
  tryAssumption : ∀ n xs → (VarsIneqInfo (suc n) xs) → (asmption : Assumption _ _ _)
            → UseAssumptionFailReason ⊎ (Σ[ (k , (P , (q , _))) ∈ (Fin (suc n)
              × IteratedHornerForms (suc n) ×
               (Σ[ q ∈ _ ] (0r` ≲[ fst (fst asmption) ] q)))  ] 
         lookup k xs ≡ eval P (q ∷ drop k xs))
  tryAssumption n xs vii ((b , ihf , mbVarToElim) , 0≲[b]ihf) = do
        let varsToTry = Mb.rec (uncurry L._++_ (partitionVarsByHavingInfo vii)) [_] mbVarToElim
            ihfN , ihfN= = normalizeIHF ihf
            q = eval ihfN xs
            ihf* = (Constant _ (- 1r) ·X+ ihfN)
            0=ihf* : 0r` ≡ eval ihf* (q ∷ xs)
            0=ihf* = sym (R`.+InvR q)
                    ∙∙ cong (q +`_) ((RT`.-IsMult-1 _)
                      ∙ cong (_·` q) ((cong (-`_) (sym pres1) ∙ sym (pres- 1r) )
                       ∙ sym (evalConstant  _ (- 1r) (q ∷ xs)))) ∙∙ R`.+Comm _ _
        (_ , isj , ihf' , ihf'=) ← maybeToSum
             [ "noElimFound" ]ₑ
             (L.findP 
                 (λ k →
                   do  (zero , u) ← mbIsolatedPowerVar ihf* (suc k)
                         where _ → nothing
                       let se = toElimination ihf* (suc k) zero u
                       mbVerySimpleElim _ ihf* (suc k) (q ∷ xs) 0=ihf* se)
                    varsToTry)
        let k = fromIsJust isj
        pure ((k , ihf' , q , subst (0r` ≲[ b ]_) (ihfN= _) 0≲[b]ihf) , ihf'= )


  eliminateStep : ∀ {ℓg} {G : Type ℓg} {n m : ℕ}  
       → Problem (suc n) IteratedHornerForms (suc m) G
       → UseAssumptionFailReason ⊎ (Problem (suc n) IteratedHornerForms m G)
  eliminateStep {n = n} {m} PRB = do
    ed ← mbEliminationHead
    pe ← preEliminate ed
    inr (eliminate ed pe)
   where
   module P = Problem PRB
   

   mbEliminationHead : UseAssumptionFailReason ⊎ Σ _ (ElimData PRB)
   mbEliminationHead with tryAssumption _ P.xs P.vii (lookup zero P.assumptions)
   ... | inl uafr = inl uafr
   ... | inr z = inr (zero , z)



   module _ ((assId , ((k , P , (q , ≲q)) , (xs[k]≡evP))) : Σ _ (ElimData PRB)) where
    open Problem
    bQ =  fst (fst (lookup assId P.assumptions))
    newXs = q ∷ Vec.drop k P.xs

    Asmptns' = (Vec (Σ[ ((_ , _ , mbK) , _) ∈ Assumption (suc n) IteratedHornerForms P.xs ]
               ¬ (mbK ≡ just k)) m)

    preEliminate :
      UseAssumptionFailReason
        ⊎ Asmptns'
    preEliminate =
      ⊎.rec (λ x → inr x)
            (λ _ → inl
              L.[ strErr "same variable in two different elimnation hints"  ])
               (dec→∀⊎¬∃
       (λ ((_ , _ , mbK) , _) → Dec¬
         (discreteMaybe discreteFin mbK (just k)))
          (Vec.drop assId (P.assumptions)))
    
    elimInAss : ∀ e
       → Σ[ e' ∈ (_) ] (eval e P.xs ≡ eval e' (drop' (suc k) (q ∷ P.xs)))
    elimInAss e  =
      let (e' , u) = substHF' (suc k) (0H ·X+ e) P
          (e'N , uN) = normalizeIHF e'
          u' = sym (uN (drop' (suc k) (q ∷ P.xs))) ∙ u (q ∷ P.xs) (sym (xs[k]≡evP))
      in e'N , (sym (RT`.+IdL' _ _ (RT`.0LeftAnnihilates _)) ∙ sym u')
    module _ (asmptns' : Asmptns') where                  
     eliminate : _
     eliminate .xs = newXs
     eliminate .vii = ≲→IneqInfo bQ ≲q , dropVarsIneqInfo k P.vii
     eliminate .assumptions = 
       Vec.map
               (λ (((b , e , mbV) , x) , mbV≢justK) → 
                  (b , fst (elimInAss e) ,
                       (Mb.elim (λ mbV → ¬ mbV ≡ just k → Maybe (Fin (suc n)))
                          (λ _ → nothing)
                          (λ k' ¬p →  just (suc (fst (punchOut {A = Unit} k k'
                             (fromWitness (¬p ∘ sym ∘ cong just)))))) mbV) mbV≢justK)
                    , subst (0r` ≲[ b ]_) (snd (elimInAss e)) x)
               asmptns' 
     eliminate .goalRel = P.goalRel
     eliminate .goalExpr = fst (elimInAss P.goalExpr)
     eliminate .solution 0≲E =
       P.solution (subst (0r` ≲[ P.goalRel ]_) (sym (snd (elimInAss P.goalExpr)))
         0≲E)
        
  foldAssumptionsS : ∀ {ℓg} {G : Type ℓg} {n m : ℕ}  
       → Problem (suc n) IteratedHornerForms m G
       → UseAssumptionFailReason ⊎ (Problem (suc n) IteratedHornerForms 0 G)
  foldAssumptionsS {m = zero} = inr
  foldAssumptionsS {m = suc m} x = eliminateStep x >>= foldAssumptionsS

  foldAssumptions : ∀ {ℓg} {G : Type ℓg} {n m : ℕ}  
       → Problem n IteratedHornerForms m G
       → UseAssumptionFailReason ⊎ (Problem n IteratedHornerForms 0 G)
  foldAssumptions {n = zero} w = inr w'
   where
   module P = Problem w
   w' : Problem zero IteratedHornerForms 0 _
   w' .Problem.xs = P.xs
   w' .Problem.vii = P.vii
   w' .Problem.assumptions = []
   w' .Problem.goalRel = P.goalRel
   w' .Problem.goalExpr = P.goalExpr
   w' .Problem.solution = P.solution
  foldAssumptions {n = suc n} = foldAssumptionsS
  

  module _ {ℓg} {G : Type ℓg} {n m : ℕ} (PRB : Problem n Polynomial m G) where
   open Problem PRB


   trySolve : FailReason ⊎ G
   trySolve =
    let pi = polyIneqInfo n goalExpr xs vii
    in ⊎.map (λ z → z) solution (IneqInfo→Mb≲ _ goalRel pi) 



    
  solveInequalityOld : ∀ (n : ℕ) b (e₀ e₁ : RExpr n) (xs : Vec (fst R`) n) →
          VarsIneqInfo n xs → (FailReason ⊎ (⟦ e₀ ⟧ xs ≲[ b ] ⟦ e₁ ⟧ xs))
  solveInequalityOld n b e₀ e₁ xs xsInfo =
   let po , u = x≲y-fromDecΣ n b e₀ e₁ xs
       
       prb = mkProblemRE n xs [] xsInfo b e₀ e₁
       p' = Problem≑> (Expr≑>IHF ∘≑> IHF≑>Poly) prb
   in trySolve p'




  solveInequality : ∀ (n : ℕ) (xs : Vec (fst R`) n)
          → (ineq : Inequality n RExpr xs)
          → List (Assumption' n xs) → VarsIneqInfo n xs → (FailReason ⊎ InequalityTy ineq)
  solveInequality n xs (inequality b e₀ e₁) assmptns  xsInfo =
   let po , u = x≲y-fromDecΣ n b e₀ e₁ xs
       
       prb = mkProblemRE n xs assmptns xsInfo b e₀ e₁
       p' = Problem≑> (Expr≑>IHF) prb
   in ⊎.rec (inl ∘ unableToUseAssumption)
      -- TODO : get rid off unncecesary normalisaiton here,
      -- it is required only for the case where there are no assumptions
      (trySolve ∘ Problem≑> (IHF≑>normalizedIHF ∘≑> IHF≑>Poly))
      (foldAssumptions p')
      
  mkInequality : ∀ (n : ℕ) → Bool → (e₀ e₁ : RExpr n) (xs : Vec (fst R`) n) → Inequality n RExpr xs
  mkInequality _ z e₀ e₁ _ = inequality z e₀ e₁

  mkInequalityProof : ∀ (n : ℕ) → (b : Bool) → (e₀ e₁ : RExpr n) (xs : Vec (fst R`) n) →
      _ → Maybe (Fin n) → Assumption' n xs
  mkInequalityProof n z e₀ e₁ xs prf k = (inequality z e₀ e₁ , k) , prf
