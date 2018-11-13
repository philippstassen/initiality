{-# OPTIONS --prop #-}

open import common
open import syntx
open import contextualcat
open import rules

module _ (C : StructuredCCat) where

open StructuredCCat C
open CCat ccat renaming (Mor to MorC)
open import partialinterpretation C

{- Predicate saying whether an object "respects" a context in the sense that the types in Γ correspond to their interpretation in X.
   We cannot use (X ≡ ⟦ Γ ⟧) instead because it fails the termination checker somehow. -}

respectsCtx : (X : Ob n) (Γ : Ctx n) → Prop
respectsCtx {zero} X ◇ = Unit
respectsCtx {suc n} X (Γ , A) = respectsCtx (ft X) Γ × Σ (isDefined (⟦ A ⟧Ty (ft X))) (λ Aᵈ → totalify (⟦ A ⟧Ty (ft X)) Aᵈ ≡ X)

{- Totality of the partial interpretation functions -}

isTotal⟦⟧Ty  : {Γ : Ctx n} (X : Ob n) (r : respectsCtx X Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) → isDefined (⟦ A ⟧Ty X)
isTotal⟦⟧Tm  : {Γ : Ctx n} (X : Ob n) (r : respectsCtx X Γ) {A : TyExpr n} {u : TmExpr n} (du : Derivable (Γ ⊢ u :> A)) → isDefined (⟦ u ⟧Tm X)
isTotal⟦⟧Mor : {Γ : Ctx n} (X : Ob n) {Δ : Ctx m} (Y : Ob m) (r : respectsCtx X Γ) (r' : respectsCtx Y Δ) {δ : Mor n m} (dδ : Γ ⊢ δ ∷> Δ) → isDefined (⟦ δ ⟧Mor X Y)

⟦⟧Ty : {Γ : Ctx n} (X : Ob n) (r : respectsCtx X Γ) {A : TyExpr n} (dA : Derivable (Γ ⊢ A)) → Ob (suc n)
⟦⟧Ty X r {A = A} dA = totalify (⟦ A ⟧Ty X) (isTotal⟦⟧Ty X r dA)

{- Various compatibilities -}

∂₀⟦⟧Mor : (X : Ob n) (Y : Ob m) (δ : Mor n m) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} → ∂₀ (totalify (⟦ δ ⟧Mor X Y) δᵈ) ≡ X
∂₁⟦⟧Mor : (X : Ob n) (Y : Ob m) (δ : Mor n m) {δᵈ : isDefined (⟦ δ ⟧Mor X Y)} → ∂₁ (totalify (⟦ δ ⟧Mor X Y) δᵈ) ≡ Y

⟦⟧Ty-ft : {X : Ob n} (A : TyExpr n) {Aᵈ : isDefined (⟦ A ⟧Ty X)} → ft (totalify (⟦ A ⟧Ty X) Aᵈ) ≡ X

⟦⟧Tm-section : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} → is-section (totalify (⟦ u ⟧Tm X) uᵈ)
⟦⟧Tm₀ : {X : Ob n} (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} → ∂₀ (totalify (⟦ u ⟧Tm X) uᵈ) ≡ X
⟦⟧Tm₁ : {Γ : Ctx n} {X : Ob n} (r : respectsCtx X Γ) (u : TmExpr n) {uᵈ : isDefined (⟦ u ⟧Tm X)} {A : TyExpr n} {Aᵈ : isDefined (⟦ A ⟧Ty X)} (du : Derivable (Γ ⊢ u :> A)) → ∂₁ (totalify (⟦ u ⟧Tm X) uᵈ) ≡ totalify (⟦ A ⟧Ty X) Aᵈ

respectsCtxExt : {Γ : Ctx n} (X : Ob n) (r : respectsCtx X Γ) (A : TyExpr n) {Aᵈ : isDefined (⟦ A ⟧Ty X)}
              → respectsCtx (totalify (⟦ A ⟧Ty X) Aᵈ) (Γ , A)
respectsCtxExt {Γ = Γ} X r A {Aᵈ} rewrite ⟦⟧Ty-ft A {Aᵈ} = r , _ , refl

{- Interpretation of definitional equalities -}

⟦⟧TyEq : {Γ : Ctx n} (X : Ob n) (r : respectsCtx X Γ) {A A' : TyExpr n} (dA= : Derivable (Γ ⊢ A == A')) (Aᵈ : isDefined (⟦ A ⟧Ty X)) (A'ᵈ : isDefined (⟦ A' ⟧Ty X))
        → totalify (⟦ A ⟧Ty X) Aᵈ ≡ totalify (⟦ A' ⟧Ty X) A'ᵈ
⟦⟧TmEq : {Γ : Ctx n} (X : Ob n) (r : respectsCtx X Γ) {A : TyExpr n} {u u' : TmExpr n} (du= : Derivable (Γ ⊢ u == u' :> A)) (uᵈ : isDefined (⟦ u ⟧Tm X)) (u'ᵈ : isDefined (⟦ u' ⟧Tm X))
        → totalify (⟦ u ⟧Tm X) uᵈ ≡ totalify (⟦ u' ⟧Tm X) u'ᵈ

{- Interpretation of total substitutions -}

⟦tsubst⟧Tyᵈ : (X : Ob n) (Y : Ob m) (A : TyExpr m) {δ : Mor n m}
            → isDefined (⟦ A ⟧Ty Y)
            → isDefined (⟦ δ ⟧Mor X Y)
            → isDefined (⟦ A [ δ ]Ty ⟧Ty X)

⟦tsubst⟧Ty= : (X : Ob n) (Y : Ob m) (A : TyExpr m)
            (Aᵈ : isDefined (⟦ A ⟧Ty Y))
            (δ : Mor n m)
            (δᵈ : isDefined (⟦ δ ⟧Mor X Y))
            → totalify (⟦ A [ δ ]Ty ⟧Ty X) (⟦tsubst⟧Tyᵈ X Y A Aᵈ δᵈ)
              ≡ star (totalify (⟦ δ ⟧Mor X Y) δᵈ) (totalify (⟦ A ⟧Ty Y) Aᵈ) (∂₁⟦⟧Mor X Y δ ∙ ! (⟦⟧Ty-ft A))

-- TODO: for terms

{- Definitions -}

isTotal⟦⟧Ty X r UU = tt
isTotal⟦⟧Ty X r {A = pi A B} (Pi dA dB) = (isTotal⟦⟧Ty X r dA , (isTotal⟦⟧Ty (⟦⟧Ty X r dA) (respectsCtxExt X r A) dB) , tt)
isTotal⟦⟧Ty X r {A = el v} (El dv) = (isTotal⟦⟧Tm X r dv , ⟦⟧Tm-section v , (⟦⟧Tm₁ r v dv ∙ ap UUStr (! (⟦⟧Tm₀ v))) , tt)

isTotal⟦⟧Tm X r (VarLast dA) = tt
isTotal⟦⟧Tm X r (VarPrev dA dx) = tt
isTotal⟦⟧Tm X r (Conv dA du dA=) = isTotal⟦⟧Tm X r du
isTotal⟦⟧Tm X r {u = lam A B u} (Lam dA dB du) =
  (isTotal⟦⟧Ty X r dA ,
   isTotal⟦⟧Tm (⟦⟧Ty X r dA) (respectsCtxExt X r A) du ,
   ⟦⟧Tm-section u , tt)
isTotal⟦⟧Tm X r {u = app A B f a} (App dA dB df da) =
  let X+ = ⟦⟧Ty X r dA
      r+ = respectsCtxExt X r A
  in
  (isTotal⟦⟧Ty X r dA ,
   isTotal⟦⟧Ty X+ r+ dB ,
   isTotal⟦⟧Tm X r df ,
   ⟦⟧Tm-section f ,
   ⟦⟧Tm₁ r f df ,
   isTotal⟦⟧Tm X r da ,
   ⟦⟧Tm-section a ,
   (⟦⟧Tm₁ r a da ∙ ! (⟦⟧Ty-ft B)) , tt)

isTotal⟦⟧Mor X {Δ = ◇} Y r r' {◇} tt = tt
isTotal⟦⟧Mor X {Δ = Δ , B} Y r r' {δ , u} (dδ , du) =
  let δᵈ = isTotal⟦⟧Mor X (ft Y) r (fst r') dδ
      Bᵈ = fst (snd r')
  in
  (δᵈ ,
   isTotal⟦⟧Tm X r du ,
   ∂₁⟦⟧Mor X (ft Y) δ ,
   (⟦⟧Tm₁ r u {Aᵈ = ⟦tsubst⟧Tyᵈ X (ft Y) B Bᵈ δᵈ} du ∙ ⟦tsubst⟧Ty= X (ft Y) B Bᵈ δ δᵈ ∙ ap2-irr star refl (snd (snd r'))) , tt)

∂₀⟦⟧Mor X Y ◇ = ptmor₀
∂₀⟦⟧Mor X Y (δ , u) = comp₀ ∙ ⟦⟧Tm₀ u

∂₁⟦⟧Mor X Y ◇ = ptmor₁ ∙ ! (pt-unique Y)
∂₁⟦⟧Mor X Y (δ , u) = comp₁ ∙ qq₁

⟦⟧Ty-ft (pi A B)  = PiStr= ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A
⟦⟧Ty-ft uu = UUStr=
⟦⟧Ty-ft (el v) = ElStr= ∙ ⟦⟧Tm₀ v

⟦⟧Tm-section (var x) = {!TODO!}
⟦⟧Tm-section (lam A B u) = lamStrs
⟦⟧Tm-section (app A B f a) = appStrs

⟦⟧Tm₀ (var x) = {!varC₀ --TODO!}
⟦⟧Tm₀ (lam A B u) = lamStr₀ (⟦⟧Tm-section u) ∙ ap ft (⟦⟧Tm₀ u) ∙ ⟦⟧Ty-ft A
⟦⟧Tm₀ (app A B f a) = appStr₀ (⟦⟧Tm-section a) _ ∙ ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A

⟦⟧Tm₁ r (var last) (VarLast du) = {!varC₁ --TODO!}
⟦⟧Tm₁ r (var (prev k)) (VarPrev du du₁) = {!varC₁ --TODO!}
⟦⟧Tm₁ r u (Conv dA du dA=) = ⟦⟧Tm₁ r u du ∙ ⟦⟧TyEq _ r dA= (isTotal⟦⟧Ty _ r dA) _
⟦⟧Tm₁ r (lam A B u) (Lam dA dB du) = lamStr₁ ∙ ap PiStr (⟦⟧Tm₁ (respectsCtxExt _ r A) u du)
⟦⟧Tm₁ r (app A B f a) (App dA dB df da) = appStr₁ ∙ ! (⟦tsubst⟧Ty= _ _ B (isTotal⟦⟧Ty _ (respectsCtxExt _ r A {Aᵈ = isTotal⟦⟧Ty _ r dA}) dB) _ ({!idMor is interpretable!} , {!stuff!}) ∙ {!⟦ a ⟧Tm = ⟦ idMor , a ⟧Mor!})

⟦⟧TyEq X r (TySymm dA=) Aᵈ A'ᵈ = ! (⟦⟧TyEq X r dA= A'ᵈ Aᵈ)
⟦⟧TyEq X r (TyTran dB dA= dB=) Aᵈ A'ᵈ = ⟦⟧TyEq X r dA= Aᵈ (isTotal⟦⟧Ty X r dB) ∙ ⟦⟧TyEq X r dB= (isTotal⟦⟧Ty X r dB) A'ᵈ
⟦⟧TyEq X r {A = pi A B} {A' = pi A' B'} (PiCong dA dA= dB=) (Aᵈ , Bᵈ , _) (A'ᵈ , B'ᵈ , _) rewrite ! (⟦⟧TyEq X r dA= Aᵈ A'ᵈ) | ! (⟦⟧TyEq _ (respectsCtxExt _ r A) dB= Bᵈ B'ᵈ)
  = refl
⟦⟧TyEq X r UUCong Aᵈ A'ᵈ = refl
⟦⟧TyEq X r (ElCong dv=) (vᵈ , _) (v'ᵈ , _) rewrite ⟦⟧TmEq X r dv= vᵈ v'ᵈ = refl

⟦⟧TmEq X r (VarLastCong dA) tt tt = refl
⟦⟧TmEq X r (VarPrevCong {k = k} {k' = k'} dA dx) tt tt = ap-irr weakenCTm (⟦⟧TmEq (ft X) (fst r) dx tt tt) {b = weakenCTm^₀ k (var-unweakened k (ft X)) (var-unweakened₀ k (ft X))} {b' = weakenCTm^₀ k' (var-unweakened k' (ft X)) (var-unweakened₀ k' (ft X))}
⟦⟧TmEq X r (TmSymm du=) uᵈ u'ᵈ = ! (⟦⟧TmEq X r du= u'ᵈ uᵈ)
⟦⟧TmEq X r (TmTran du= du'=) uᵈ u'ᵈ = ⟦⟧TmEq X r du= uᵈ {!add as argument to TmTran!} ∙ ⟦⟧TmEq X r du'= {!add as argument to TmTran!} u'ᵈ
⟦⟧TmEq X r (ConvEq dA' du= dA=) uᵈ u'ᵈ = ⟦⟧TmEq X r du= uᵈ u'ᵈ
⟦⟧TmEq X r {u = lam A B u} (LamCong dA dA= dB= du=) (Aᵈ , uᵈ , utmᵈ , _) (A'ᵈ , u'ᵈ , utm'ᵈ , _)
  rewrite ! (⟦⟧TyEq X r dA= Aᵈ A'ᵈ)
        | ! (⟦⟧TmEq (totalify (⟦ A ⟧Ty X) Aᵈ) (respectsCtxExt X r A) du= uᵈ u'ᵈ) = refl
⟦⟧TmEq X r {u = app A B f a} (AppCong dA dA= dB= df= da=) (Aᵈ , Bᵈ , fᵈ , _ , _ , aᵈ , _) (A'ᵈ , B'ᵈ , f'ᵈ , _ , _ , a'ᵈ , _)
  rewrite ! (⟦⟧TyEq X r dA= Aᵈ A'ᵈ)
           | ⟦⟧TyEq (totalify (⟦ A ⟧Ty X) Aᵈ) (respectsCtxExt X r A) dB= Bᵈ B'ᵈ
           | ⟦⟧TmEq X r df= fᵈ f'ᵈ
           | ⟦⟧TmEq X r da= aᵈ a'ᵈ = refl
⟦⟧TmEq X r (Beta dA dB du da) (Aᵈ , Bᵈ , (_ , _ , uᵈ , _) , aᵈ , _) u'ᵈ = {!betaStr ∙ ?!}


⟦tsubst⟧Tyᵈ X Y (pi A B) {δ = δ} (Aᵈ , Bᵈ , tt) δᵈ =
  (⟦tsubst⟧Tyᵈ X Y A Aᵈ δᵈ ,
   ⟦tsubst⟧Tyᵈ (totalify (⟦ A [ δ ]Ty ⟧Ty X) (⟦tsubst⟧Tyᵈ X Y A Aᵈ δᵈ)) (totalify (⟦ A ⟧Ty Y) Aᵈ) B Bᵈ {!⟦ weakenMor δ , var last ⟧ is defined!}
  , tt)
⟦tsubst⟧Tyᵈ X Y uu tt δᵈ = tt
⟦tsubst⟧Tyᵈ X Y (el v) (vᵈ , vTy , _) δᵈ = {!⟦tsubst⟧Tmᵈ X Y v vᵈ δᵈ  --TODO!} , {!stuff!}

⟦tsubst⟧Ty= X Y (pi A B) (Aᵈ , Bᵈ , tt) δ δᵈ = ! (PiStrNat (totalify (⟦ δ ⟧Mor X Y) δᵈ) {p = (ap ft (⟦⟧Ty-ft B) ∙ ⟦⟧Ty-ft A) ∙ ! (∂₁⟦⟧Mor X Y δ)} ∙ {!annoying recursive calls!})
⟦tsubst⟧Ty= X Y uu Aᵈ δ δᵈ = ! (UUStrNat (totalify (⟦ δ ⟧Mor X Y) δᵈ) {p = ! (∂₁⟦⟧Mor X Y δ)} ∙ ap UUStr (∂₀⟦⟧Mor X Y δ))
⟦tsubst⟧Ty= X Y (el v) Aᵈ δ δᵈ = ! (ElStrNat (totalify (⟦ δ ⟧Mor X Y) δᵈ) {p = ⟦⟧Tm₀ v ∙ ! (∂₁⟦⟧Mor X Y δ)} ∙ ap-irr2 ElStr {!⟦tsubst⟧Tm=  --TODO!})
