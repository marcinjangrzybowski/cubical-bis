module Cubical.Tactics.CommRingSolver.OrderedReflection where

open import Cubical.Foundations.Prelude hiding (Type)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String
open import Agda.Builtin.Nat using () renaming (_==_ to _=ℕ_)

open import Cubical.Reflection.Base

open import Cubical.Data.Maybe as Mb
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
import Cubical.Data.FinData as Fin
open import Cubical.Data.List as L
open import Cubical.Data.Nat.Literals

open import Cubical.Data.Int as Slowℤ using (fromNegℤ; fromNatℤ)
open import Cubical.Data.Nat using (ℕ; discreteℕ) renaming (_+_ to _+ℕ_)
open import Cubical.Data.NatPlusOne
import Cubical.Data.Nat as ℕ
open import Cubical.Data.Bool
open import Cubical.Data.Vec using (Vec) renaming ([] to emptyVec; _∷_ to _∷vec_)

open import Cubical.Relation.Nullary.Base

open import Cubical.Algebra.CommRing

import Cubical.Algebra.CommRing.Properties as CommRingProperties
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Tactics.CommRingSolver.AlgebraExpression

open import Cubical.Tactics.CommRingSolver.Solver
open import Cubical.Tactics.CommRingSolver.Config
open import Cubical.Tactics.CommRingSolver.GenericCommRing
open import Cubical.Reflection.Sugar
open import Cubical.Tactics.Reflection
open import Cubical.Tactics.Reflection.Variables
open import Cubical.Tactics.Reflection.Error
open import Cubical.Tactics.Reflection.Utilities
open import Cubical.Tactics.Reflection.Utilities using (quoteDefsfNames;ω[];_ω∷_;_][_) public
open import Cubical.Tactics.Reflection.Goals

open import Cubical.Data.Int using (ℤ;pos;negsuc)
import Cubical.Data.Fast.Int as Fastℤ
import Cubical.Data.Fast.Int.Order as ℤ
import Cubical.Algebra.CommRing.Instances.Fast.Int as Fastℤ'
import Cubical.Algebra.OrderedCommRing
import Cubical.Algebra.OrderedCommRing.Instances.Rationals as OrderedRats
import Cubical.Algebra.OrderedCommRing.Instances.Fast.Int as OrderedFastℤ

-- import Cubical.Data.Rationals as ℚ
-- import Cubical.Algebra.CommRing.Instances.Rationals as ℚ'
import Cubical.HITs.SetQuotients as SetQuotient

open import Cubical.Data.List.Dependent as DL using (_∷_ ; P[_] ; []) public
import Cubical.Algebra.AbGroup.Base as AbGroup

open import Cubical.Tactics.CommRingSolver.Config

open import Cubical.Tactics.CommRingSolver.Reflection
open import Cubical.Tactics.CommRingSolver.OrderedSolver
open import Cubical.Tactics.CommRingSolver.OrderedConfig

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Properties
import Cubical.Tactics.CommRingSolver.Specialised.Rationals as Rat
import Cubical.Data.Rationals as Rat
import Cubical.Data.Rationals.Order as Rat
import Cubical.Data.Rationals.Order.Properties as Rat

import Cubical.Data.Prod as Prod


infix 55 _↘_

opaque
 _↘_ : ∀ {ℓ} {A B : Type ℓ} → A → B → A Prod.× B
 _↘_ = Prod._,_
 
showFailReason : FailReason →  List ErrorPart
showFailReason (tooWeak x) = [ strErr x ]
showFailReason (missingInfo x) =
  "missingInfo:\n\n" ∷ₑ L.join (L.map (λ {
     (noInfoMsg s) →  "no infoMsg: " ∷ₑ s ∷nl []
   ; (noVarInfo k) →   "no info about var: " ∷ₑ " varId:" ∷ₑ mkNiceVar k ∷nl []
    } ) x)
showFailReason (unableToUseAssumption x) =  "unableToUseAssumption: " ∷ₑ x

module OrderedCommRingSolver (ocrs : OrderedCommRingSolverConfig) where

 open OrderedCommRingSolverConfig ocrs
 open CommRingSolver commRingSolverConfig
 open CommRingReflection
 nicelyVars : Vars → List ErrorPart
 nicelyVars = L.join ∘
  L.map (λ (k , tm) →  "\n" ∷ₑ mkNiceVar k ∷ₑ " ∶ " ∷ₑ [ tm ]ₑ) ∘
   zipWithIndex


 IneqData = (Bool × (Term × Term))

 IneqProofData = ((Bool × (Term × Term)) × Term) × Term


 nicelyShowGoal : Vars -> IneqData → TC _
 nicelyShowGoal vars (rel , lhs' , rhs') = do
   lhs'' ← prettyExpr (length vars) lhs'
   rhs'' ← prettyExpr (length vars) rhs'
   
   pure ((" vars: " ∷nl (nicelyVars vars
                   ++nl "\nGOAL:" ∷nl (lhs'' ∷nl (if rel then "<" else "≤") ∷nl [ rhs'' ]ₑ))))

 

 private
  variableList : Vars → Arg Term
  variableList [] = varg (con (quote emptyVec) [])
  variableList (t ∷ ts)
    = varg (con (quote _∷vec_) (t v∷ (variableList ts) ∷ []))
    
  ≲solverCallWithVars : ℕ → Vars → IneqData → Term → List IneqProofData  → Term → Term
  ≲solverCallWithVars n vars (rel , (lhs , rhs)) OCRSC asmptnsList varsIneqInfo =
    let ineq = def (quote SansReflectionOreded.Decidable≲.mkInequality)
              (OCRSC v∷ (ℕAsTerm n) v∷ (con (if rel then quote true else quote false) []) v∷ lhs v∷ rhs
               v∷ (variableList vars) ∷ [])
        asmptnsT = toListTerm (L.map
           (λ (((rel , (lhs , rhs)) , prf) , mbElimVar) →
               def (quote SansReflectionOreded.Decidable≲.mkInequalityProof)
              (OCRSC v∷ (ℕAsTerm n) v∷ (con (if rel then quote true else quote false) []) v∷ lhs v∷ rhs
               v∷ (variableList vars) ∷ prf v∷ mbElimVar v∷ []))
           asmptnsList)
    in def (quote SansReflectionOreded.Decidable≲.solveInequality)
          (OCRSC v∷ (ℕAsTerm n) v∷ (variableList vars) ∷ ineq v∷ asmptnsT v∷ v[ varsIneqInfo ] )


 

 record IneqInCtx : Type where
  constructor ineqInCtx
  field
   proofTerm : Term
   strict? : Bool
   lhs rhs : Term



  
 matchTyInCtx :
    (ℕ × String) × Term → TC (Maybe IneqInCtx) --(Maybe (Term × (Bool × (Term × Term))))
 matchTyInCtx ((k , _) , tm) = map-Maybe (uncurry (uncurry ∘ ((uncurry ∘_) ∘ ineqInCtx))) <$> (do
   nothing ← normalise tm >>= mkMatchInequalityGoalTC 
    where just x → pure (just (var k [] , x))
   (map-Maybe ((def (quote snd) v[ var k [] ]) ,_)
    <$> (inferType (def (quote snd) v[ var k [] ]) >>= normalise
           >>= mkMatchInequalityGoalTC)) <|> pure nothing)
   -- mkMatchInequalityGoalTC tm'

 inferIneqsInCtx : TC (List IneqInCtx)
 inferIneqsInCtx = do
   ctx ← getContext'
   catMaybes <$> mapM ((matchTyInCtx ∘S (map-snd unArg)) >=>
    Mb.rec (pure nothing) λ (ineqInCtx tmk rel lhs rhs) →
      just <$> (ineqInCtx tmk rel <$> pure lhs <*> pure rhs)) ctx
    
 macro
  ineqsInCtx : Term → TC Unit
  ineqsInCtx tm = do
    uu ←  (L.join ∘S  L.map (λ (ineqInCtx tmk rel lhs rhs) →
             (tmk ∷ₑ " : " ∷ₑ lhs ∷ₑ (if rel then "<" else "≤") ∷ₑ rhs  ∷ₑ [ "\n" ]ₑ )))
            <$> inferIneqsInCtx 
    typeError $ "ineqs in ctx: \n" ∷ₑ uu

 -- noInfoVarIneqInfo : Term → Vars → TC Term
 -- noInfoVarIneqInfo _ [] = pure unknown
 -- noInfoVarIneqInfo ocrsTerm (x ∷ x₁) = do
 --  a ← noInfoVarIneqInfo ocrsTerm  x₁
 --  pure (con (quote _,_) ((def (quote (SansReflectionOreded.noInfo'))
 --   (ocrsTerm v∷ v[ lit (string "no inferedInfo") ]))
 --   v∷ v[ a ]))


 collectInfoFromCtx : Term → Vars → TC Term
 collectInfoFromCtx ocrsTerm vars = do
   ineqInfoType ← normalise $ def (quote SansReflectionOreded.VarsIneqInfo)
          (ocrsTerm v∷ (ℕAsTerm (length vars)) v∷ [ variableList vars ])
   -- typeError [ ineqInfoType ]ₑ
   noInfoIneqInfoTm ←   -- 
    (checkType (def (quote SansReflectionOreded.varsIneqNoInfo)
          (ocrsTerm v∷ (ℕAsTerm (length vars)) v∷ [ variableList vars ])) (ineqInfoType))
   
   ictx ← inferIneqsInCtx
   

   -- ineqInfoTm ← withReduceDefs (false , [])
   --   (foldlM infoFromSigmasStep noInfoIneqInfoTm (zipWithIndex vars))

   withReduceDefs (false , [])
     (foldlM cifcStep noInfoIneqInfoTm ictx) -- >>= flip checkType (ineqInfoType))
   -- typeError [ ineqInfoTm ]ₑ
  where
   -- infoFromSigmasStep : Term → (ℕ × Term) → TC Term
   -- infoFromSigmasStep t v =
   --   {!tryPairFromFst v!}
   -- infoFromSigmasStep t _ = pure t
   
   cifcStep : Term → IneqInCtx → TC Term
   cifcStep t iic = do
     just ((b , prfTm) , k) ← (maybeVarIneqInfo vars)
       where nothing → (pure t)
     bTm ← quoteTC b >>= normalise
     kTm ← quoteTC k >>= normalise
     pure $ def (quote SansReflectionOreded.setVarsIneqInfo')
       ((ocrsTerm v∷ (ℕAsTerm (length vars)) v∷ variableList vars ∷
          kTm v∷ bTm v∷ prfTm v∷ v[ t ]))
    where
    open IneqInCtx iic

    maybeVarIneqInfo : (v : Vars) →  TC (Maybe ((Bool × Term) × _)) 
    maybeVarIneqInfo vrs = do
     is0 ← mbPureMatchZero lhs
     pure $ if is0 
      then ((strict? , proofTerm) ,_) <$> indexOfFin rhs vrs
      else nothing
      -- (withReconstructed true (unify 0r`Tm lhs) >> 
      --  pure (((strict? , proofTerm) ,_) <$> indexOfFin rhs vrs)) <|> pure nothing


 quoteIneqType : Term → TC (Abstr IneqData)
 quoteIneqType goal = do
   be ← mkBuildExpr
   just (rel , lhs , rhs) ← mkMatchInequalityGoalTC goal
     where nothing → typeError $  "not an inequality : " ∷ₑ [ goal ]ₑ
   -- typeError ("inequality " ∷ₑ (if rel then "<" else "≤") ∷nl lhs ∷nl [ rhs ]ₑ) 
   -- lhs' <- withNormalisation true $ checkType lhs
   -- rhs' <- normalise rhs
   amapM₂ (λ x y →  rel , x , y) (be lhs) (be rhs)

 quoteIneqProof : Term → TC (Abstr IneqProofData)
 quoteIneqProof (def (quote _↘_) xs) = do
   just (prf , vh) ← pure (tryGetTwoVArgs xs)
    where nothing → typeError [ "imposible in quoteIneqProof" ]ₑ
   ty ← inferType prf >>= normalise
   amapM₂ (λ x y →  (x , prf) , y)
    (quoteIneqType ty) (pure (abstrVarId vh))
   -- amap ((_, (con (quote nothing) [])) ∘ (_, prf)) <$> (quoteIneqType ty)
   -- ty ← inferType prf >>= normalise
   -- amap ((_, (con (quote nothing) [])) ∘ (_, prf)) <$> (quoteIneqType ty)
 quoteIneqProof prf = do
   ty ← inferType prf >>= normalise
   amap ((_, (con (quote nothing) [])) ∘ (_, prf)) <$> (quoteIneqType ty)
  


 <≤!-macro : Term → List Term → Bool → TC Unit
 <≤!-macro hole asmptionsTms justShow = withReduceDefs (false ,
     (quote SansReflectionOreded.Decidable≲.x≲y-fromDec) ∷ doNotUnfold) do
   goal ← inferType hole >>= normalise
   -- wait-for-term goal
   -- just (rel , lhs , rhs) ← mkMatchInequalityGoalTC goal
   --   where nothing → typeError [ "not an inequality" ]ₑ
   -- -- typeError ("inequality " ∷ₑ (if rel then "<" else "≤") ∷nl lhs ∷nl [ rhs ]ₑ) 
   -- (lhs' , rhs' , vars) ← toAlgebraExpr (lhs , rhs)
   ((goalIneqData , assmptionsIneqData) , vars) ← assignFst <$>
     ( amapM₂ _,_ (quoteIneqType goal)
        (aForM asmptionsTms quoteIneqProof))
   ocrsTerm ← quoteωTC ocrs
   -- (lemH , _) ← newHole
 
   ineqInfoTm ← collectInfoFromCtx ocrsTerm vars
   if justShow then (typeError []) else (pure tt)
   -- assmptsTm ← pure (con (quote L.[]) [])
   nothing ← (withReduceDefs (false , []) $
     unifyRight hole (≲solverCallWithVars (length vars) vars goalIneqData ocrsTerm
         assmptionsIneqData ineqInfoTm))
      <|> (do
           nrmSol ← normalise (≲solverCallWithVars
                 (length vars) vars goalIneqData ocrsTerm
                      assmptionsIneqData ineqInfoTm)
           (typeError ("failedToUnquoteSum :" ∷nl [ nrmSol ]ₑ)))
    where just failReasonStr → do
              
              nsg ← nicelyShowGoal vars goalIneqData
              asmptnsNice ← concatMapM ((_<$>_ (" \n\n  " ∷ₑ_))
               ∘ nicelyShowGoal vars ∘ fst ∘ fst) assmptionsIneqData
              typeError (([ "failWithReason: " ] ++ₑ (showFailReason failReasonStr) ) ++nl nsg ++nl
                asmptnsNice)
   pure _
   -- sTy ← inferType solution >>= normalise
   -- lTy ← inferType lemH >>= normalise
   -- checkType lem lTy
   -- unify lem lemH
   -- typeError [ solution ]ₑ
   -- solutionN ← normalise solution 
   -- if justShow
   --  then (typeError [ solution ]ₑ)
   --  else (unify solution hole)
   
   -- 
   
 macro
  <≤! : Term → TC Unit
  <≤! hole = <≤!-macro hole [] false

  prev-<≤! : Term → TC Unit
  prev-<≤! hole = <≤!-macro hole [] true
   


  <≤![_] : Term → Term → TC Unit
  <≤![_] assumptions hole = <≤!-macro hole (prodToTermList assumptions) false

 
module WithOrdering {rℓ rℓ`} (crsc : CommRingSolverConfig) where
 open CommRingSolverConfig crsc
 module _  (ordering : RingOrdering rℓ R)
           (ordering` : RingOrdering rℓ` R`) where
  OR = Iso.inv IsoΣRingOrdering (R , ordering) 
  OR` = Iso.inv IsoΣRingOrdering (R` , ordering`)

  module ORS = OrderedCommRingStr (snd OR)
  module ORS` = OrderedCommRingStr (snd OR`)

  -- tryMatchRelDef : Name → Term → TC (Term × Term)
  -- tryMatchRelDef n tm = do
  --   (lhs , _) ← newHole
  --   (rhs , _) ← newHole
  --   unify (def n (lhs v∷ v[ rhs ])) tm
  --   lhs ← normalise lhs
  --   rhs ← normalise rhs
  --   pure (lhs , rhs)

  -- tryMatchRelDef : Name → Term → TC (Term × Term)
  -- tryMatchRelDef = {!!}




  module _
           (scalar`≤ : _)
           (scalar`< : _) (scalar`<-refl : _) (dec< : _) (dec≤ : _) (≡<>??  : _)
           (mbInv : _) (mbPureMatch0 : _) (nm< nm≤ : Name) where

   matchIneqTy : (Name × List (Arg Term)) → Maybe (Bool × (Term × Term))
   matchIneqTy (nm , args) =
     _,_ <$>
       (if (nm == nm<) then just true
      else if (nm == nm≤) then just false
       else nothing)
         <*> tryGetTwoVArgs args
     
     --   else (if (nm == nm≤) then just (false , lrhs) else nothing)
     
   open OrderedCommRingSolverConfig
   ocrsc : OrderedCommRingSolverConfig
   ocrsc .commRingSolverConfig =
    record crsc { doNotUnfold = nm< ∷ nm≤ ∷ crsc .doNotUnfold }
   ocrsc .oℓ = _
   ocrsc .oℓ` = _
   ocrsc ._<_ = _
   ocrsc .OrderedCommRingSolverConfig._≤_ = _
   ocrsc ._<?_ = dec<
   ocrsc ._≤?_ = dec≤
   ocrsc .≡<>? = ≡<>??
   ocrsc .iocr = ORS.isOrderedCommRing
   ocrsc ._<`_ = _
   ocrsc ._≤`_ = _
   ocrsc .iocr` = ORS`.isOrderedCommRing
   ocrsc .pres< = scalar`< 
   ocrsc .pres≤ = scalar`≤
   ocrsc .reflect< = scalar`<-refl
   ocrsc .mbInverses = mbInv
   ocrsc .mbPureMatchZero = mbPureMatch0
   ocrsc .mkMatchInequalityGoalTC tm =
     pure ((tryGetName tm) >>= matchIneqTy)
   
     -- (just <$> (((true ,_) <$> (tryMatchRelDef nm< tm)) <|> ((false ,_) <$> (tryMatchRelDef nm≤ tm))))
     --   <|> (pure nothing)



module OrederedSolverRationals where
  hasInvs : (∀ x y k → 0 Rat.< k → (k Rat.· x) Rat.< y → Σ _ λ 1/k → x Rat.< (1/k Rat.· y))
               × (∀ x y k → 0 Rat.< k → (k Rat.· x) Rat.≤ y → Σ _ λ 1/k → x Rat.≤ (1/k Rat.· y))
  hasInvs .fst x y k 0<k p = (fst (Rat.invℚ₊ (k , 0<k))) ,
   subst (x Rat.<_) (Rat.·Comm y _) (Rat.y·x<z→x<z·invℚ₊y x y (k , 0<k) p)
  hasInvs .snd x y k 0<k p = (fst (Rat.invℚ₊ (k , 0<k))) ,
   subst (x Rat.≤_) (Rat.·Comm y _) (Rat.y·x≤z→x≤z·invℚ₊y x y (k , 0<k) p)

  0ℚraw : Rat.ℚ
  0ℚraw = Rat.[ pos ℕ.zero , (1+ ℕ.zero) ]

  0ℚ-term = q[ 0ℚraw ]

  0ℚtrmTest : Term → Bool
  -- 0ℚtrmTest (con (quote SetQuotient.[_])
  --    (_ ∷ _ ∷ _ ∷ _ ∷
  --     v[ con (quote _,_) (_ ∷ _ ∷ _ ∷ _ ∷ con _ v[ lit (nat ℕ.zero) ]
  --          v∷ v[ con _ v[ _ ] ]) ]))  =
  --        true
  0ℚtrmTest (con (quote SetQuotient.[_])
     (_ ∷ _ ∷ _ ∷ _ ∷
      v[ con (quote _,_) (_ ∷ _ ∷ _ ∷ _ ∷ con _ v[ lit (nat ℕ.zero) ]
           v∷ v[ con (quote 1+_) v[ lit (nat ℕ.zero) ] ]) ]))  =
         true
  0ℚtrmTest _ = false

  0ℚtrmTestTC : Term → TC Bool
  0ℚtrmTestTC tm = do
    just tm' ← Rat.mbConcreteℚ tm
     where nothing → --typeError [ tm ]ₑ
             pure false
    pure (0ℚtrmTest tm')

  0ℚtrmTestTC2 : Term → TC Bool
  0ℚtrmTestTC2 tm = 
    ((unify
       0ℚ-term tm) >> 
       pure true) <|> pure false


  
  ocrsc = WithOrdering.ocrsc Rat.config (_ ,
   snd (OrderedRats.ℚOrderedCommRing) .OrderedCommRingStr.isOrderedCommRing)
    ((_ ,
   snd (OrderedRats.ℚOrderedCommRing) .OrderedCommRingStr.isOrderedCommRing))
   (λ _ _ z → z) (λ _ _ z → z) (λ _ _ z → z)
   Rat.<Dec Rat.≤Dec Rat.≡⊎# (just hasInvs)
     0ℚtrmTestTC (quote Rat._<_) (quote Rat._≤_)
   -- (quote Rat._<_) (quote Rat._≤_)

  open OrderedCommRingSolver ocrsc public
  
open OrederedSolverRationals using ()
 renaming (prev-<≤! to prev-<≤ℚ! ; <≤! to <≤ℚ! ; <≤![_] to <≤ℚ![_] ; ineqsInCtx to ineqsInCtxℚ) public

module OrederedSolverInt where

 ≡⊎#ℤ : ∀ x y → (x ≡ y) ⊎ ((x ℤ.< y) ⊎ (y ℤ.< x))
 ≡⊎#ℤ x y with (x ℤ.≟ y)
 ... | ℤ.lt x₁ = inr (inl x₁)
 ... | ℤ.eq x₁ = inl x₁
 ... | ℤ.gt x₁ = inr (inr x₁)

 is0TC? : Term → TC Bool
 is0TC? (con (quote pos) v[ lit (nat ℕ.zero) ]) = pure true
 is0TC? _ = pure false
 
 ocrscℤ = WithOrdering.ocrsc FastℤRingSolver.config
  (snd (Iso.fun IsoΣRingOrdering OrderedFastℤ.ℤOrderedCommRing)) (snd (Iso.fun IsoΣRingOrdering
   OrderedFastℤ.ℤOrderedCommRing))
  (λ _ _ z → z) (λ _ _ z → z) (λ _ _ z → z)
   ℤ._<?_ ℤ._≤?_ ≡⊎#ℤ nothing
  is0TC? --(λ _ → pure false)
  (quote ℤ._<_) (quote ℤ._≤_) 

 open OrderedCommRingSolver ocrscℤ public


open OrederedSolverInt using ()
 renaming (prev-<≤! to prev-<≤ℤ! ; <≤! to <≤ℤ! ; <≤![_] to <≤ℤ![_] ; ineqsInCtx to ineqsInCtxℤ) public

