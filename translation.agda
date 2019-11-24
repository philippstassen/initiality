{-# OPTIONS --rewriting --prop --without-K #-}

open import common renaming (UnitR to metaUnit)
open import normal
import ex 
open ex.shared
open ex.Judgment renaming (_⊢_ to _⊢ₑ_) renaming (_⊢_:>_ to _⊢ₑ_:>_) renaming (_⊢_==_ to _⊢ₑ_==_) renaming (_⊢_==_:>_ to _⊢ₑ_==_:>_)

||_||Ty : {n : ℕ} → ex.TyExpr n → TyExpr n
||_||Tm : {n : ℕ} → ex.TmExpr n → TmExpr n

|| ex.uu i ||Ty = uu i
|| ex.el i v ||Ty = el i (|| v ||Tm)
|| ex.pi σ σ₁ ||Ty = pi (|| σ ||Ty) (|| σ₁ ||Ty)
-- || ex.sig σ σ₁ ||Ty = sig (|| σ ||Ty) (|| σ₁ ||Ty)
-- || ex.empty ||Ty = empty
-- || ex.unit ||Ty = unit
-- || ex.nat ||Ty = nat
-- || ex.id σ u v ||Ty = id (|| σ ||Ty) (|| u ||Tm) (|| v ||Tm)

|| ex.var x ||Tm = var x
-- || ex.uu i ||Tm = uu i
-- || ex.pi i t t₁ ||Tm = pi i (|| t ||Tm) (|| t₁ ||Tm)
|| ex.lam A B t ||Tm = lam (|| A ||Ty) (|| B ||Ty) (|| t ||Tm)
|| ex.app A B t t₁ ||Tm = app (|| A ||Ty) (|| B ||Ty) (|| t ||Tm) (|| t₁ ||Tm)
-- || ex.sig i t t₁ ||Tm = sig i (|| t ||Tm) (|| t₁ ||Tm)
-- || ex.pair A B t t₁ ||Tm = pair (|| A ||Ty) (|| B ||Ty) (|| t ||Tm) (|| t₁ ||Tm)
-- || ex.pr1 A B t ||Tm = pr1 (|| A ||Ty) (|| B ||Ty) (|| t ||Tm)
-- || ex.pr2 A B t ||Tm = pr2 (|| A ||Ty) (|| B ||Ty) (|| t ||Tm)
-- || ex.empty i ||Tm = empty i
-- || ex.emptyelim A t ||Tm =  emptyelim (|| A ||Ty) (|| t ||Tm)
-- || ex.unit i ||Tm = unit i
-- || ex.tt ||Tm = tt
-- || ex.unitelim A t t₁ ||Tm = unitelim (|| A ||Ty) (|| t ||Tm) (|| t₁ ||Tm)
-- || ex.nat i ||Tm = nat i
-- || ex.zero ||Tm = zero
-- || ex.suc t ||Tm = suc || t ||Tm
-- || ex.natelim P t t₁ t₂ ||Tm =  natelim (|| P ||Ty) (|| t ||Tm) (|| t₁ ||Tm) (|| t₂ ||Tm)
-- || ex.id i t t₁ t₂ ||Tm = id i (|| t ||Tm) (|| t₁ ||Tm) (|| t₂ ||Tm)
-- || ex.refl A t ||Tm = refl (|| A ||Ty) (|| t ||Tm)
-- || ex.jj A P t t₁ t₂ t₃ ||Tm =  jj (|| A ||Ty) (|| P ||Ty) (|| t ||Tm) (|| t₁ ||Tm) (|| t₂ ||Tm) (|| t₃ ||Tm)
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
|| Γ ⊢ x ≃ x₁ || = || Γ ||Ctx ⊢ || x ||Ty == || x₁ ||Ty 

{- weakening commutes with stripping -}
WeakenVar'CommStrip : (k : Fin (suc n)) → (l : Fin n) → ex.weakenVar' k l ≡ weakenVar' k l
WeakenVar'CommStrip last l = refl
WeakenVar'CommStrip (prev k) last = refl
WeakenVar'CommStrip (prev k) (prev l) = ap prev (WeakenVar'CommStrip k l)

WeakenTy'CommStrip : (k : Fin (suc n)) → (A : ex.TyExpr n) → || ex.weakenTy' k A ||Ty ≡ weakenTy' k (|| A ||Ty)
WeakenTm'CommStrip : (k : Fin (suc n)) → (u : ex.TmExpr n) → || ex.weakenTm' k u ||Tm ≡ weakenTm' k (|| u ||Tm)

WeakenTy'CommStrip k (ex.uu i) = refl
WeakenTy'CommStrip k (ex.el i v) rewrite WeakenTm'CommStrip k v = refl
WeakenTy'CommStrip k (ex.pi A A₁) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) A₁ = refl
-- WeakenTy'CommStrip k (ex.sig A A₁) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) A₁ = refl
-- WeakenTy'CommStrip k ex.empty = refl
-- WeakenTy'CommStrip k ex.unit = refl
-- WeakenTy'CommStrip k ex.nat = refl
-- WeakenTy'CommStrip k (ex.id A u v) rewrite WeakenTy'CommStrip k A | WeakenTm'CommStrip k u | WeakenTm'CommStrip k v = refl

WeakenTm'CommStrip k (ex.var x) rewrite WeakenVar'CommStrip k x = refl
-- WeakenTm'CommStrip k (ex.uu i) = refl
-- WeakenTm'CommStrip k (ex.pi i u u₁) rewrite WeakenTm'CommStrip k u | WeakenTm'CommStrip (prev k) u₁ = refl
WeakenTm'CommStrip k (ex.lam A B u) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) B | WeakenTm'CommStrip (prev k) u = refl
WeakenTm'CommStrip k (ex.app A B u u₁) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) B | WeakenTm'CommStrip k u | WeakenTm'CommStrip k u₁ = refl
-- WeakenTm'CommStrip k (ex.sig i u u₁) rewrite WeakenTm'CommStrip k u | WeakenTm'CommStrip (prev k) u₁ = refl
-- WeakenTm'CommStrip k (ex.pair A B u u₁) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) B | WeakenTm'CommStrip k u | WeakenTm'CommStrip k u₁ = refl
-- WeakenTm'CommStrip k (ex.pr1 A B u) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) B | WeakenTm'CommStrip k u = refl
-- WeakenTm'CommStrip k (ex.pr2 A B u) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) B | WeakenTm'CommStrip k u = refl
-- WeakenTm'CommStrip k (ex.empty i) = refl
-- WeakenTm'CommStrip k (ex.emptyelim A u) rewrite WeakenTy'CommStrip (prev k) A | WeakenTm'CommStrip k u = refl
-- WeakenTm'CommStrip k (ex.unit i) = refl
-- WeakenTm'CommStrip k ex.tt = refl
-- WeakenTm'CommStrip k (ex.unitelim A u u₁) rewrite WeakenTy'CommStrip (prev k) A | WeakenTm'CommStrip k u | WeakenTm'CommStrip k u₁ = refl
-- WeakenTm'CommStrip k (ex.nat i) = refl
-- WeakenTm'CommStrip k ex.zero = refl
-- WeakenTm'CommStrip k (ex.suc u) = ap suc (WeakenTm'CommStrip k u)
-- WeakenTm'CommStrip k (ex.natelim P u u₁ u₂) rewrite WeakenTy'CommStrip (prev k) P | WeakenTm'CommStrip k u | WeakenTm'CommStrip (prev (prev k)) u₁ | WeakenTm'CommStrip k u₂ = refl
-- WeakenTm'CommStrip k (ex.id i u u₁ u₂) rewrite WeakenTm'CommStrip k u | WeakenTm'CommStrip k u₁ | WeakenTm'CommStrip k u₂ = refl
-- WeakenTm'CommStrip k (ex.refl A u) rewrite WeakenTy'CommStrip k A | WeakenTm'CommStrip k u = refl
-- WeakenTm'CommStrip k (ex.jj A P u u₁ u₂ u₃) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev (prev (prev k))) P | WeakenTm'CommStrip (prev k) u | WeakenTm'CommStrip k u₁ | WeakenTm'CommStrip k u₂ | WeakenTm'CommStrip k u₃ = refl
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

[]TyCommStrip (ex.uu i) δ = refl
[]TyCommStrip (ex.el i v) δ = ap-el-Ty refl ([]TmCommStrip v δ)
[]TyCommStrip (ex.pi A A₁) δ rewrite ([]TyCommStrip A₁ (ex.weakenMor+ δ)) | weakenMor+CommStrip δ = ap-pi-Ty ([]TyCommStrip A δ) refl
-- []TyCommStrip (ex.sig A A₁) δ rewrite ([]TyCommStrip A₁ (ex.weakenMor+ δ)) | weakenMor+CommStrip δ = ap-sig-Ty ([]TyCommStrip A δ) refl
-- []TyCommStrip ex.empty δ = refl
-- []TyCommStrip ex.unit δ = refl
-- []TyCommStrip ex.nat δ = refl
-- []TyCommStrip (ex.id A u v) δ = ap-id-Ty ([]TyCommStrip A δ) ([]TmCommStrip u δ) ([]TmCommStrip v δ)

[]TmCommStrip (ex.var x) δ = []VarCommStrip x δ
-- []TmCommStrip (ex.uu i) δ = refl
-- []TmCommStrip (ex.pi i u u₁) δ rewrite ([]TmCommStrip u₁ (ex.weakenMor+ δ)) | weakenMor+CommStrip δ = ap-pi-Tm refl ([]TmCommStrip u δ) refl
[]TmCommStrip (ex.lam A B u) δ rewrite ([]TyCommStrip B (ex.weakenMor+ δ)) | ([]TmCommStrip u (ex.weakenMor+ δ)) | weakenMor+CommStrip δ = ap-lam-Tm ([]TyCommStrip A δ) refl refl
[]TmCommStrip (ex.app A B u u₁) δ rewrite ([]TyCommStrip B (ex.weakenMor+ δ)) | weakenMor+CommStrip δ = ap-app-Tm ([]TyCommStrip A δ) refl ([]TmCommStrip u δ) ([]TmCommStrip u₁ δ)
-- -- []TmCommStrip (ex.sig i u u₁) δ rewrite ([]TmCommStrip u₁ (ex.weakenMor+ δ)) | weakenMor+CommStrip δ = ap-sig-Tm refl ([]TmCommStrip u δ) refl
-- -- []TmCommStrip (ex.pair A B u u₁) δ rewrite ([]TyCommStrip B (ex.weakenMor+ δ)) | weakenMor+CommStrip δ = ap-pair-Tm ([]TyCommStrip A δ) refl ([]TmCommStrip u δ) ([]TmCommStrip u₁ δ)
-- -- []TmCommStrip (ex.pr1 A B u) δ rewrite ([]TyCommStrip B (ex.weakenMor+ δ)) | weakenMor+CommStrip δ = ap-pr1-Tm ([]TyCommStrip A δ) refl ([]TmCommStrip u δ)
-- -- []TmCommStrip (ex.pr2 A B u) δ rewrite ([]TyCommStrip B (ex.weakenMor+ δ)) | weakenMor+CommStrip δ = ap-pr2-Tm ([]TyCommStrip A δ) refl ([]TmCommStrip u δ)
-- -- []TmCommStrip (ex.empty i) δ = refl
-- -- []TmCommStrip (ex.emptyelim A u) δ rewrite ([]TyCommStrip A (ex.weakenMor+ δ)) | weakenMor+CommStrip δ = ap-emptyelim-Tm refl ([]TmCommStrip u δ)
-- -- []TmCommStrip (ex.unit i) δ = refl
-- -- []TmCommStrip ex.tt δ = refl
-- -- []TmCommStrip (ex.unitelim A u u₁) δ rewrite ([]TyCommStrip A (ex.weakenMor+ δ)) | weakenMor+CommStrip δ = ap-unitelim-Tm refl ([]TmCommStrip u δ) ([]TmCommStrip u₁ δ)
-- -- []TmCommStrip (ex.nat i) δ = refl
-- -- []TmCommStrip ex.zero δ = refl
-- -- []TmCommStrip (ex.suc u) δ = ap-suc-Tm ([]TmCommStrip u δ)
-- -- []TmCommStrip (ex.natelim P u u₁ u₂) δ rewrite ([]TyCommStrip P (ex.weakenMor+ δ)) | weakenMor+CommStrip δ | []TmCommStrip u₁ (ex.weakenMor+^ 2 δ) | weakenMor+CommStrip (ex.weakenMor+ δ) | weakenMorCommStrip δ = ap-natelim-Tm refl ([]TmCommStrip u δ) refl ([]TmCommStrip u₂ δ)
-- -- []TmCommStrip (ex.id i u u₁ u₂) δ = ap-id-Tm refl ([]TmCommStrip u δ) ([]TmCommStrip u₁ δ) ([]TmCommStrip u₂ δ)
-- -- []TmCommStrip (ex.refl A u) δ = ap-refl-Tm ([]TyCommStrip A δ) ([]TmCommStrip u δ)
-- -- []TmCommStrip (ex.jj A P u u₁ u₂ u₃) δ rewrite []TyCommStrip P (ex.weakenMor+^ 3 δ) | []TmCommStrip u (ex.weakenMor+ δ) | weakenMor+^3CommStrip δ | weakenMor+CommStrip δ
-- --                        = ap-jj-Tm ([]TyCommStrip A δ) refl refl ([]TmCommStrip u₁ δ) ([]TmCommStrip u₂ δ) ([]TmCommStrip u₃ δ)
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

-- subst3Ty-weakenprev3CommStrip : {n : ℕ} → (P : ex.TyExpr (suc (suc (suc n)))) → (A : ex.TyExpr n) → || ex.subst3Ty (ex.weakenTy' (prev (prev (prev last))) P) (ex.var last) (ex.var last) ({!!}) ||Ty ≡ subst3Ty (weakenTy' (prev (prev (prev last))) || P ||Ty) (var last) (var last) ({!!})
-- -- refl (ex.weakenTy A) (ex.var last)
-- -- refl (weakenTy || A ||Ty) (var last)
-- subst3Ty-weakenprev3CommStrip P A rewrite subst3TyCommStrip (ex.weakenTy' (prev (prev (prev last))) P) (ex.var last) (ex.var last) ({!!}) | WeakenTy'CommStrip (prev (prev (prev last))) P | WeakenTyCommStrip A = {!!}
-- refl (ex.weakenTy A) (ex.var last)
-- Stripping respects derivability 
DerToNormal : {judg : ex.Judgment} → (ex.Derivation judg) → (Derivation (|| judg ||))
DerToNormal (ex.VarLast {A = A} dj) rewrite WeakenTyCommStrip A = VarLast (DerToNormal dj)
DerToNormal (ex.VarPrev {A = A} dj dj₁) rewrite WeakenTyCommStrip A = VarPrev (DerToNormal dj) (DerToNormal dj₁)
DerToNormal (ex.VarLastCong {A = A} dj) rewrite WeakenTyCommStrip A = VarLastCong (DerToNormal dj)
DerToNormal (ex.VarPrevCong {A = A} dj dj₁) rewrite WeakenTyCommStrip A = VarPrevCong (DerToNormal dj) (DerToNormal dj₁)
DerToNormal (ex.TySymm dj) = TySymm (DerToNormal dj)
DerToNormal (ex.TyTran dj dj₁ dj₂) = TyTran (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
DerToNormal (ex.TmSymm dj) = TmSymm (DerToNormal dj)
DerToNormal (ex.TmTran dj dj₁ dj₂) = TmTran (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
DerToNormal (ex.Conv dj dj₁ dj₂) = Conv (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
DerToNormal (ex.ConvEq dj dj₁ dj₂) = ConvEq (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
DerToNormal (ex.CoercRefl {u = u} dj) = TmRefl (DerToNormal dj)
DerToNormal (ex.CoercRefl! dj) = TmRefl (DerToNormal dj)
DerToNormal (ex.CoercTrans dj dj₁ dj₂ dj₃ dj₄) = TmRefl (Conv (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₄))
DerToNormal ex.UU = UU
DerToNormal ex.UUCong = UUCong
-- DerToNormal ex.UUUU = UUUU
-- DerToNormal ex.UUUUCong = UUUUCong
-- DerToNormal ex.ElUU= = ElUU=
DerToNormal (ex.El dj) = El (DerToNormal dj)
DerToNormal (ex.ElCong dj) = ElCong (DerToNormal dj)
DerToNormal (ex.Pi dj dj₁) = Pi (DerToNormal dj) (DerToNormal dj₁)
DerToNormal (ex.PiCong dj dj₁ dj₂) = PiCong (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
-- DerToNormal (ex.PiUU dj dj₁) =  PiUU (DerToNormal dj) (DerToNormal dj₁)
-- DerToNormal (ex.PiUUCong dj dj₁ dj₂) = PiUUCong (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
-- DerToNormal (ex.ElPi= dj dj₁) = ElPi= (DerToNormal dj) (DerToNormal dj₁)
DerToNormal (ex.Lam dj dj₁ dj₂) = Lam (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
DerToNormal (ex.LamCong dj dj₁ dj₂ dj₃) = LamCong (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂) (DerToNormal dj₃)
DerToNormal (ex.App {B = B} {a = a} dj dj₁ dj₂ dj₃) rewrite (substTyCommStrip B a) = App (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂) (DerToNormal dj₃)
DerToNormal (ex.AppCong {B = B} {a = a} dj dj₁ dj₂ dj₃ dj₄) rewrite (substTyCommStrip B a) = AppCong (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂) (DerToNormal dj₃) (DerToNormal dj₄)
-- DerToNormal (ex.Sig dj dj₁) = Sig (DerToNormal dj) (DerToNormal dj₁)
-- DerToNormal (ex.SigCong dj dj₁ dj₂) = SigCong (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
-- DerToNormal (ex.SigUU dj dj₁) = SigUU (DerToNormal dj) (DerToNormal dj₁)
-- DerToNormal (ex.SigUUCong dj dj₁ dj₂) = SigUUCong (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
-- DerToNormal (ex.ElSig= dj dj₁) = ElSig= (DerToNormal dj) (DerToNormal dj₁)
-- DerToNormal (ex.Pair {B = B} {a = a} dj dj₁ dj₂ dj₃) = Pair (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂) (congTmTy (substTyCommStrip B a) (DerToNormal dj₃))
-- DerToNormal (ex.PairCong {B = B} {a = a} dj dj₁ dj₂ dj₃ dj₄) = PairCong (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂) (DerToNormal dj₃) (congTmEqTy (substTyCommStrip B a) (DerToNormal dj₄))
-- DerToNormal (ex.Pr1 dj dj₁ dj₂) = Pr1 (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
-- DerToNormal (ex.Pr1Cong dj dj₁ dj₂ dj₃) = Pr1Cong (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂) (DerToNormal dj₃)
-- DerToNormal (ex.Pr2 {A = A} {B = B} {u = u} dj dj₁ dj₂) = congTmTy (! (substTyCommStrip B (ex.pr1 A B u))) (Pr2 (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂))
-- DerToNormal (ex.Pr2Cong {A = A} {B = B} {u = u} dj dj₁ dj₂ dj₃) = congTmEqTy (! (substTyCommStrip B (ex.pr1 A B u))) (Pr2Cong (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂) (DerToNormal dj₃))
-- DerToNormal ex.Empty = Empty
-- DerToNormal ex.EmptyCong = EmptyCong
-- DerToNormal ex.EmptyUU = EmptyUU
-- DerToNormal ex.EmptyUUCong = EmptyUUCong
-- DerToNormal ex.ElEmpty= = ElEmpty=
-- DerToNormal (ex.Emptyelim {A = A} {u = u} dj dj₁) = congTmTy! (substTyCommStrip A u) (Emptyelim (DerToNormal dj) (DerToNormal dj₁))
-- DerToNormal (ex.EmptyelimCong {A = A} {u = u} dj dj₁) =  congTmEqTy! (substTyCommStrip A u) (EmptyelimCong (DerToNormal dj) (DerToNormal dj₁))
-- DerToNormal ex.Unit = Unit
-- DerToNormal ex.UnitCong = UnitCong
-- DerToNormal ex.UnitUU = UnitUU
-- DerToNormal ex.UnitUUCong = UnitUUCong
-- DerToNormal ex.ElUnit= = ElUnit=
-- DerToNormal ex.TT = TT
-- DerToNormal ex.TTCong = TTCong
-- DerToNormal (ex.Unitelim {A = A} {u = u} dj dj₁ dj₂) = congTmTy! (substTyCommStrip A u) (Unitelim (DerToNormal dj) (congTmTy (substTyCommStrip A ex.tt) (DerToNormal dj₁)) (DerToNormal dj₂))
-- DerToNormal (ex.UnitelimCong {A = A} {u = u} dj dj₁ dj₂) =  congTmEqTy! (substTyCommStrip A u) (UnitelimCong (DerToNormal dj) (congTmEqTy (substTyCommStrip A ex.tt) (DerToNormal dj₁)) (DerToNormal dj₂))

-- DerToNormal ex.Nat = Nat
-- DerToNormal ex.NatCong = NatCong
-- DerToNormal ex.NatUU = NatUU
-- DerToNormal ex.NatUUCong = NatUUCong
-- DerToNormal ex.ElNat= = ElNat=
-- DerToNormal ex.Zero = Zero
-- DerToNormal ex.ZeroCong = ZeroCong
-- DerToNormal (ex.Suc dj) = Suc (DerToNormal dj)
-- DerToNormal (ex.SucCong dj) = SucCong (DerToNormal dj)
-- DerToNormal (ex.Natelim {P = P} {u = u} dj dj₁ dj₂ dj₃) = congTmTy! (substTyCommStrip P u) (Natelim (DerToNormal dj) (congTmTy (substTyCommStrip P ex.zero) (DerToNormal dj₁)) (congTmTy (substTyCommStrip (ex.weakenTy' (prev last) (ex.weakenTy' (prev last) P)) (ex.suc (ex.var (prev last))) ∙ ap (λ x → substTy x (suc (var (prev last)))) ( weakenprev^2CommStrip P)) (DerToNormal dj₂)) (DerToNormal dj₃))
-- DerToNormal (ex.NatelimCong {P = P} {u = u} dj dj₁ dj₂ dj₃ dj₄) = congTmEqTy! (substTyCommStrip P u) (NatelimCong (DerToNormal dj) (DerToNormal dj₁) (congTmEqTy (substTyCommStrip P ex.zero) (DerToNormal dj₂)) (congTmEqTy ( (substTyCommStrip (ex.weakenTy' (prev last) (ex.weakenTy' (prev last) P)) (ex.suc (ex.var (prev last))) ∙ ap (λ x → substTy x (suc (var (prev last)))) ( weakenprev^2CommStrip P)) ) (DerToNormal dj₃)) (DerToNormal dj₄))
-- DerToNormal (ex.Id dj dj₁ dj₂) = Id (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
-- DerToNormal (ex.IdCong dj dj₁ dj₂) = IdCong (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
-- DerToNormal (ex.IdUU dj dj₁ dj₂) = IdUU (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
-- DerToNormal (ex.IdUUCong dj dj₁ dj₂) = IdUUCong (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
-- DerToNormal (ex.ElId= dj dj₁ dj₂) = ElId= (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)
-- DerToNormal (ex.Refl dj dj₁) = Refl (DerToNormal dj) (DerToNormal dj₁)
-- DerToNormal (ex.ReflCong dj dj₁) = ReflCong (DerToNormal dj) (DerToNormal dj₁)
-- DerToNormal (ex.JJ {Γ = Γ} {A = A} {P = P} dj dj₁ dj₂ dj₃ dj₄ dj₅) rewrite (WeakenTyCommStrip A) = congTmTy! (subst3TyCommStrip P _ _ _) (JJ (DerToNormal dj) (congTyCtx (Ctx+= (Ctx+= refl (WeakenTyCommStrip A)) (ap-id-Ty (weakenTy^2CommStrip A) refl refl)) (DerToNormal dj₁)) (congTmTy (subst3Ty-weakenprev3CommStrip P A) (DerToNormal dj₂)) (DerToNormal dj₃) (DerToNormal dj₄) (DerToNormal dj₅))
-- DerToNormal (ex.JJCong {Γ = Γ} {A = A} {P = P} dj dj₁ dj₂ dj₃ dj₄ dj₅ dj₆) = congTmEqTy! (subst3TyCommStrip _ _ _ _) (JJCong (DerToNormal dj) (DerToNormal dj₁) (congTyCtxEq (Ctx+= (Ctx+= refl (WeakenTyCommStrip A)) ( ap-id-Ty (weakenTy^2CommStrip A) refl refl)) (DerToNormal dj₂)) ( congTmEqTy (subst3Ty-weakenprev3CommStrip P A) (DerToNormal dj₃)) (DerToNormal dj₄) (DerToNormal dj₅) (DerToNormal dj₆))
DerToNormal (ex.BetaPi {B = B} {u = u} {a = a} dj dj₁ dj₂ dj₃) = congTmEqTy! (substTyCommStrip B a) (congTmEqTm refl (! (substTmCommStrip u a)) (BetaPi (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂) (DerToNormal dj₃)))
-- DerToNormal (ex.BetaSig1 dj dj₁ dj₂ dj₃) = BetaSig1 (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂) (congTmTy (substTyCommStrip _ _) (DerToNormal dj₃))
-- DerToNormal (ex.BetaSig2 dj dj₁ dj₂ dj₃) = congTmEqTy! (substTyCommStrip _ _) (BetaSig2 (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂) (congTmTy (substTyCommStrip _ _) (DerToNormal dj₃)))
-- DerToNormal (ex.BetaUnit {A = A} {dtt = dtt} dj dj₁) = congTmEqTy! (substTyCommStrip A ex.tt) (BetaUnit (DerToNormal dj) (congTmTy (substTyCommStrip A ex.tt) (DerToNormal dj₁)))
-- DerToNormal (ex.BetaNatZero {P = P} dj dj₁ dj₂) = congTmEqTy! (substTyCommStrip P ex.zero) (BetaNatZero (DerToNormal dj) (congTmTy (substTyCommStrip P ex.zero) (DerToNormal dj₁)) (congTmTy ((substTyCommStrip (ex.weakenTy' (prev last) (ex.weakenTy' (prev last) P)) (ex.suc (ex.var (prev last)))) ∙ ap (λ x → substTy x (suc (var (prev last)))) (weakenprev^2CommStrip P)) (DerToNormal dj₂)))
-- DerToNormal (ex.BetaNatSuc {P = P} {dO = dO} {dS = dS} {u = u} dj dj₁ dj₂ dj₃) = congTmEq! refl (subst2TmCommStrip dS u (ex.natelim P dO dS u)) (substTyCommStrip P (ex.suc u)) (BetaNatSuc (DerToNormal dj) (congTmTy (substTyCommStrip P ex.zero) (DerToNormal dj₁)) (congTmTy ( (substTyCommStrip (ex.weakenTy' (prev last) (ex.weakenTy' (prev last) P)) (ex.suc (ex.var (prev last)))) ∙  ap (λ x → substTy x (suc (var (prev last)))) (weakenprev^2CommStrip P)) (DerToNormal dj₂)) (DerToNormal dj₃))
-- DerToNormal (ex.BetaIdRefl {A = A} {P = P} {d = d} {a = a} dj dj₁ dj₂ dj₃) = congTmEq! refl (substTmCommStrip d a) (subst3TyCommStrip P a a (ex.refl A a)) (BetaIdRefl (DerToNormal dj) (congTyCtx (Ctx+= (Ctx+= refl (WeakenTyCommStrip _)) (ap-id-Ty (WeakenTyCommStrip (ex.weakenTy _) ∙ ap weakenTy (WeakenTyCommStrip _)) refl refl)) (DerToNormal dj₁)) (congTmTy (subst3Ty-weakenprev3CommStrip _ _) (DerToNormal dj₂)) (DerToNormal dj₃))
DerToNormal (ex.EtaPi {A = A} {B = B} {f = f} dj dj₁ dj₂) = congTmEq! refl (ap (lam || A ||Ty || B ||Ty) (ap-app-Tm (WeakenTyCommStrip A) (WeakenTy'CommStrip (prev last) B) (WeakenTmCommStrip f) refl)) refl (EtaPi (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂))
-- DerToNormal (ex.EtaSig dj dj₁ dj₂) = EtaSig (DerToNormal dj) (DerToNormal dj₁) (DerToNormal dj₂)

SquashCtx : {Γ : ex.Ctx n} → ex.⊢ Γ → ⊢ || Γ ||Ctx
SquashCtx {Γ = ex.◇} dΓ = starU
SquashCtx {Γ = Γ ex., A} (dΓ , dA) = SquashCtx dΓ , DerToNormal dA
