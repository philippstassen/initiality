{-# OPTIONS --rewriting --prop --allow-unsolved-metas #-}

open import common renaming (Unit to metaUnit)
open import normal
import ex 
open ex.shared
open ex.Judgment renaming (_⊢_ to _⊢ₑ_) renaming (_⊢_:>_ to _⊢ₑ_:>_) renaming (_⊢_==_ to _⊢ₑ_==_) renaming (_⊢_==_:>_ to _⊢ₑ_==_:>_)

||_||Ty : {n : ℕ} → ex.TyExpr n → TyExpr n
||_||Tm : {n : ℕ} → ex.TmExpr n → TmExpr n

|| ex.uu ||Ty = uu
|| ex.el v ||Ty = el (|| v ||Tm)
|| ex.pi σ σ₁ ||Ty = pi (|| σ ||Ty) (|| σ₁ ||Ty)

|| ex.var x ||Tm = var x
|| ex.lam A B t ||Tm = lam (|| A ||Ty) (|| B ||Ty) (|| t ||Tm)
|| ex.app A B t t₁ ||Tm = app (|| A ||Ty) (|| B ||Ty) (|| t ||Tm) (|| t₁ ||Tm)
|| ex.coerc S T t ||Tm = || t ||Tm

||_||Ctx : {n : ℕ} → ex.Ctx n → Ctx n
|| ex.◇ ||Ctx = ◇
|| Γ ex., A ||Ctx = || Γ ||Ctx , || A ||Ty

||_||Mor : {n m : ℕ} → ex.Mor n m → Mor n m
|| ex.◇ ||Mor = ◇
|| δ ex., u ||Mor = || δ ||Mor , || u ||Tm

||_|| : ex.Judgment → Judgment
|| Γ ⊢ₑ x || = || Γ ||Ctx ⊢ || x ||Ty
|| Γ ⊢ₑ x :> x₁ || = || Γ ||Ctx ⊢ || x ||Tm :> || x₁ ||Ty
|| Γ ⊢ₑ x == x₁ || = || Γ ||Ctx ⊢ || x ||Ty == || x₁ ||Ty
|| Γ ⊢ₑ x == x₁ :> x₂ || = || Γ ||Ctx ⊢ || x ||Tm == || x₁ ||Tm :> || x₂ ||Ty

{- weakening commutes with stripping -}
WeakenVar'CommStrip : (k : Fin (suc n)) → (l : Fin n) → ex.weakenVar' k l ≡ weakenVar' k l
WeakenVar'CommStrip last l = refl
WeakenVar'CommStrip (prev k) last = refl
WeakenVar'CommStrip (prev k) (prev l) = ap prev (WeakenVar'CommStrip k l)

WeakenTy'CommStrip : (k : Fin (suc n)) → (A : ex.TyExpr n) → || ex.weakenTy' k A ||Ty ≡ weakenTy' k (|| A ||Ty)
WeakenTm'CommStrip : (k : Fin (suc n)) → (u : ex.TmExpr n) → || ex.weakenTm' k u ||Tm ≡ weakenTm' k (|| u ||Tm)

WeakenTy'CommStrip k (ex.uu) = refl
WeakenTy'CommStrip k (ex.el v) rewrite WeakenTm'CommStrip k v = refl
WeakenTy'CommStrip k (ex.pi A A₁) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) A₁ = refl

WeakenTm'CommStrip k (ex.var x) rewrite WeakenVar'CommStrip k x = refl
WeakenTm'CommStrip k (ex.lam A B u) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) B | WeakenTm'CommStrip (prev k) u = refl
WeakenTm'CommStrip k (ex.app A B u u₁) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) B | WeakenTm'CommStrip k u | WeakenTm'CommStrip k u₁ = refl
WeakenTm'CommStrip k (ex.coerc S T u) rewrite WeakenTm'CommStrip k u = refl

WeakenTyCommStrip : (A : ex.TyExpr n) → || ex.weakenTy A ||Ty ≡ weakenTy (|| A ||Ty)
WeakenTmCommStrip : (u : ex.TmExpr n) → || ex.weakenTm u ||Tm ≡ weakenTm (|| u ||Tm)

WeakenTyCommStrip A = WeakenTy'CommStrip last A
WeakenTmCommStrip u = WeakenTm'CommStrip last u

weakenTy^2CommStrip : {n : ℕ} → (A : ex.TyExpr n) → || ex.weakenTy (ex.weakenTy A) ||Ty ≡ weakenTy (weakenTy || A ||Ty)
weakenTy^2CommStrip A = WeakenTyCommStrip (ex.weakenTy A) ∙ ap weakenTy (WeakenTyCommStrip A)

-- Weakening of Morphism
weakenMor'CommStrip : (k : Fin (suc n)) → (δ : ex.Mor n m) → || ex.weakenMor' k δ ||Mor ≡ weakenMor' k || δ ||Mor

weakenMor'CommStrip k ex.◇ = refl
weakenMor'CommStrip k (δ ex., u) rewrite weakenMor'CommStrip k δ | WeakenTm'CommStrip k u = refl

weakenMorCommStrip : (δ : ex.Mor n m) → || ex.weakenMor δ ||Mor ≡ weakenMor || δ ||Mor
weakenMorCommStrip δ = weakenMor'CommStrip last δ

weakenMor+CommStrip : (δ : ex.Mor n m) → || ex.weakenMor+ δ ||Mor ≡ weakenMor+ || δ ||Mor
weakenMor+CommStrip δ rewrite weakenMorCommStrip δ = refl

weakenMor+^2CommStrip : (δ : ex.Mor n m) → || ex.weakenMor+^ 2 δ ||Mor ≡ weakenMor+^ 2 || δ ||Mor
weakenMor+^2CommStrip δ rewrite weakenMorCommStrip (ex.weakenMor δ) | weakenMorCommStrip δ = refl

weakenMor+^3CommStrip : (δ : ex.Mor n m) → || ex.weakenMor+^ 3 δ ||Mor ≡ weakenMor+^ 3 || δ ||Mor
weakenMor+^3CommStrip δ rewrite weakenMorCommStrip (ex.weakenMor+^ 2 δ) | weakenMorCommStrip (ex.weakenMor δ) | weakenMorCommStrip δ = refl

weakenprev^2CommStrip : {n : ℕ} → (A : ex.TyExpr (suc n)) → || ex.weakenTy' (prev last) (ex.weakenTy' (prev last) A) ||Ty ≡ weakenTy' (prev last) (weakenTy' (prev last) (|| A ||Ty))
weakenprev^2CommStrip A = WeakenTy'CommStrip (prev last)(ex.weakenTy' (prev last) A) ∙ ap (weakenTy' (prev last)) (WeakenTy'CommStrip (prev last) A)

-- idMor commutes with stripping
idMorCommStrip : (n : ℕ) → || ex.idMor n ||Mor ≡ idMor n
idMorCommStrip zero = refl
idMorCommStrip (suc n) = weakenMor+CommStrip (ex.idMor n) ∙ ap (weakenMor+) (idMorCommStrip n)

-- Total Substitution commutes with stripping
[]VarCommStrip : (k : Fin m) → (δ : ex.Mor n m) → || k ex.[ δ ]Var ||Tm ≡ k [ || δ ||Mor ]Var
[]VarCommStrip last (δ ex., u) = refl
[]VarCommStrip (prev k) (δ ex., u) = []VarCommStrip k δ

[]TyCommStrip : (A : ex.TyExpr m) → (δ : ex.Mor n m) → || A ex.[ δ ]Ty ||Ty ≡ || A ||Ty [ || δ ||Mor ]Ty
[]TmCommStrip : (u : ex.TmExpr m) → (δ : ex.Mor n m) → || u ex.[ δ ]Tm ||Tm ≡ || u ||Tm [ || δ ||Mor ]Tm

[]TyCommStrip (ex.uu) δ = refl
[]TyCommStrip (ex.el v) δ = ap-el-Ty ([]TmCommStrip v δ)
[]TyCommStrip (ex.pi A A₁) δ rewrite ([]TyCommStrip A₁ (ex.weakenMor+ δ)) | weakenMor+CommStrip δ = ap-pi-Ty ([]TyCommStrip A δ) refl

[]TmCommStrip (ex.var x) δ = []VarCommStrip x δ
[]TmCommStrip (ex.lam A B u) δ rewrite ([]TyCommStrip B (ex.weakenMor+ δ)) | ([]TmCommStrip u (ex.weakenMor+ δ)) | weakenMor+CommStrip δ = ap-lam-Tm ([]TyCommStrip A δ) refl refl
[]TmCommStrip (ex.app A B u u₁) δ rewrite ([]TyCommStrip B (ex.weakenMor+ δ)) | weakenMor+CommStrip δ = ap-app-Tm ([]TyCommStrip A δ) refl ([]TmCommStrip u δ) ([]TmCommStrip u₁ δ)
[]TmCommStrip (ex.coerc S T u) δ = []TmCommStrip u δ

-- Partial substitution commutes with Strip
substTyCommStrip : {n : ℕ} → (A : ex.TyExpr (suc n)) → (t : ex.TmExpr n) → || ex.substTy A t ||Ty ≡ substTy (|| A ||Ty) (|| t ||Tm)
substTyCommStrip {n = n} A t rewrite ! (idMorCommStrip n) = []TyCommStrip A ((ex.idMor _) ex., t)

substTmCommStrip : {n : ℕ} → (u : ex.TmExpr (suc n)) → (t : ex.TmExpr n) → || ex.substTm u t ||Tm ≡ substTm (|| u ||Tm) (|| t ||Tm)
substTmCommStrip {n = n} u t rewrite ! (idMorCommStrip n) = []TmCommStrip u ((ex.idMor _) ex., t)

subst2TyCommStrip : {n : ℕ} → (A : ex.TyExpr (suc (suc n))) → (u v : ex.TmExpr n) → || ex.subst2Ty A u v ||Ty ≡ subst2Ty (|| A ||Ty) (|| u ||Tm) (|| v ||Tm)
subst2TyCommStrip {n = n} A u v rewrite ! (idMorCommStrip n) = []TyCommStrip A (((ex.idMor _) ex., u) ex., v )

subst2TmCommStrip : {n : ℕ} → (t : ex.TmExpr (suc (suc n))) → (u v : ex.TmExpr n) → || ex.subst2Tm t u v ||Tm ≡ subst2Tm (|| t ||Tm) (|| u ||Tm) (|| v ||Tm)
subst2TmCommStrip {n = n} t u v rewrite ! (idMorCommStrip n) = []TmCommStrip t (((ex.idMor _) ex., u) ex., v )

subst3TyCommStrip : {n : ℕ} → (A : ex.TyExpr (suc (suc (suc n)))) → (u v w : ex.TmExpr n) → || ex.subst3Ty A u v w ||Ty ≡ subst3Ty (|| A ||Ty) (|| u ||Tm) (|| v ||Tm) (|| w ||Tm)
subst3TyCommStrip {n = n} A u v w rewrite ! (idMorCommStrip n) = []TyCommStrip A ((((ex.idMor _) ex., u) ex., v) ex., w)

||coercTy|| : (B : ex.TyExpr (suc n)) (A A' : ex.TyExpr n) → || ex.coercTy B A A' ||Ty ≡ || B ||Ty
||coercTy|| B A A' = []TyCommStrip B _ ∙ ap (λ z → || B ||Ty [ z ]Ty) (idMorCommStrip _) ∙ [idMor]Ty (|| B ||Ty)

||coercTm|| : (u : ex.TmExpr (suc n)) (A A' : ex.TyExpr n) → || ex.coercTm u A A' ||Tm ≡ || u ||Tm
||coercTm|| u A A' = []TmCommStrip u _ ∙ ap (λ z → || u ||Tm [ z ]Tm) (idMorCommStrip _) ∙ [idMor]Tm (|| u ||Tm)

||coercTm^2|| : (u : ex.TmExpr (suc n)) (B : ex.TyExpr (suc n)) (A A' : ex.TyExpr  n) → || ex.coerc (ex.coercTy B A A') B (ex.coercTm u A A') ||Tm ≡ || u ||Tm
||coercTm^2|| u B A A' = ||coercTm|| u A A'

DerToNormal : {judg : ex.Judgment} → (ex.Derivable judg) → (Derivable (|| judg ||))
DerToNormal (ex.VarLast {A = A} dj) rewrite WeakenTyCommStrip A = VarLast (DerToNormal dj)
DerToNormal (ex.VarPrev {A = A} dj dj₁) rewrite WeakenTyCommStrip A = VarPrev (DerToNormal dj) (DerToNormal dj₁)
DerToNormal (ex.TyRefl dA) = TyRefl (DerToNormal dA)
DerToNormal (ex.TySymm dj) = TySymm (DerToNormal dj)
DerToNormal (ex.TyTran dj dj₁ dj₂) = TyTran (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
DerToNormal (ex.TmRefl du) = TmRefl (DerToNormal du)
DerToNormal (ex.TmSymm dj) = TmSymm (DerToNormal dj)
DerToNormal (ex.TmTran dj dj₁ dj₂) = TmTran (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
DerToNormal (ex.Conv dA dB du dA=) = Conv (DerToNormal dA) (DerToNormal dB) (DerToNormal du) (DerToNormal dA=)
DerToNormal (ex.ConvEq dj dj₁ dj₂) = ConvEq (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
DerToNormal (ex.CoercRefl {u = u} dj) = TmRefl (DerToNormal dj)
DerToNormal (ex.CoercRefl! dj) = TmRefl (DerToNormal dj)
DerToNormal (ex.CoercTrans dA dB dC du dA= dB=) = TmRefl (Conv (DerToNormal dA) (DerToNormal dC) (DerToNormal du) (TyTran (DerToNormal dB) (DerToNormal dA=) (DerToNormal dB=) ))
DerToNormal ex.UU = UU
DerToNormal ex.UUCong = UUCong
DerToNormal (ex.El dj) = El (DerToNormal dj)
DerToNormal (ex.ElCong dj) = ElCong (DerToNormal dj)
DerToNormal (ex.Pi dj dj₁) = Pi (DerToNormal dj) (DerToNormal dj₁)
DerToNormal (ex.PiCong {A = A} {A' = A'} {B' = B'} dA dA' dB dB' dA= dB=) rewrite ! (||coercTy|| B' A' A) = PiCong (DerToNormal dA) (DerToNormal dA=) (DerToNormal dB=)
DerToNormal (ex.Lam dj dj₁ dj₂) = Lam (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
DerToNormal (ex.LamCong {A = A} {A' = A'} {B' = B'} {u' = u'} dA dA' dB dB' du du' dA= dB= du=) rewrite ! (||coercTy|| B' A' A) | ! (||coercTm^2|| u' B' A' A) = LamCong (DerToNormal dA) (DerToNormal dA=) (DerToNormal dB=) (DerToNormal du=)
DerToNormal (ex.App {B = B} {a = a} dj dj₁ dj₂ dj₃) rewrite (substTyCommStrip B a) = App (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂) (DerToNormal dj₃)
DerToNormal (ex.AppCong {A = A} {A' = A'} {B = B} {B' = B'} {a = a} dA dA' dB dB' df df' da da' dA= dB= df= da=) rewrite (substTyCommStrip B a) | ! (||coercTy|| B' A' A) = AppCong (DerToNormal dA) (DerToNormal dA=) (DerToNormal dB=) (DerToNormal df=) (DerToNormal da=)
DerToNormal (ex.BetaPi {B = B} {u = u} {a = a} dj dj₁ dj₂ dj₃) = congTmEqTy! (substTyCommStrip B a) (congTmEqTm refl (! (substTmCommStrip u a)) (BetaPi (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂) (DerToNormal dj₃)))
DerToNormal (ex.EtaPi {A = A} {B = B} {f = f} dj dj₁ dj₂) = congTmEq! refl (ap (lam || A ||Ty || B ||Ty) (ap-app-Tm (WeakenTyCommStrip A) (WeakenTy'CommStrip (prev last) B) (WeakenTmCommStrip f) refl)) refl (EtaPi (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂))



