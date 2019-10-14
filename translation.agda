{-# OPTIONS --rewriting --prop --without-K #-}

open import common renaming (Unit to metaUnit)
open import normal
import ex 
open ex.shared
open ex.Judgment renaming (_⊢_ to _⊢ₑ_) renaming (_⊢_:>_ to _⊢ₑ_:>_) renaming (_⊢_==_ to _⊢ₑ_==_) renaming (_⊢_==_:>_ to _⊢ₑ_==_:>_)

||_||Ty : {n : ℕ} → ex.TyExpr n → TyExpr n
||_||Tm : {n : ℕ} → ex.TmExpr n → TmExpr n

|| ex.uu i ||Ty = uu i
|| ex.el i v ||Ty = el i (|| v ||Tm)
|| ex.pi σ σ₁ ||Ty = pi (|| σ ||Ty) (|| σ₁ ||Ty)
|| ex.sig σ σ₁ ||Ty = sig (|| σ ||Ty) (|| σ₁ ||Ty)
|| ex.empty ||Ty = empty
|| ex.unit ||Ty = unit
|| ex.nat ||Ty = nat
|| ex.id σ u v ||Ty = id (|| σ ||Ty) (|| u ||Tm) (|| v ||Tm)

|| ex.var x ||Tm = var x
|| ex.uu i ||Tm = uu i
|| ex.pi i t t₁ ||Tm = pi i (|| t ||Tm) (|| t₁ ||Tm)
|| ex.lam A B t ||Tm = lam (|| A ||Ty) (|| B ||Ty) (|| t ||Tm)
|| ex.app A B t t₁ ||Tm = app (|| A ||Ty) (|| B ||Ty) (|| t ||Tm) (|| t₁ ||Tm)
|| ex.sig i t t₁ ||Tm = sig i (|| t ||Tm) (|| t₁ ||Tm)
|| ex.pair A B t t₁ ||Tm = pair (|| A ||Ty) (|| B ||Ty) (|| t ||Tm) (|| t₁ ||Tm)
|| ex.pr1 A B t ||Tm = pr1 (|| A ||Ty) (|| B ||Ty) (|| t ||Tm)
|| ex.pr2 A B t ||Tm = pr2 (|| A ||Ty) (|| B ||Ty) (|| t ||Tm)
|| ex.empty i ||Tm = empty i
|| ex.emptyelim A t ||Tm =  emptyelim (|| A ||Ty) (|| t ||Tm)
|| ex.unit i ||Tm = unit i
|| ex.tt ||Tm = tt
|| ex.unitelim A t t₁ ||Tm = unitelim (|| A ||Ty) (|| t ||Tm) (|| t₁ ||Tm)
|| ex.nat i ||Tm = nat i
|| ex.zero ||Tm = zero
|| ex.suc t ||Tm = suc || t ||Tm
|| ex.natelim P t t₁ t₂ ||Tm =  natelim (|| P ||Ty) (|| t ||Tm) (|| t₁ ||Tm) (|| t₂ ||Tm)
|| ex.id i t t₁ t₂ ||Tm = id i (|| t ||Tm) (|| t₁ ||Tm) (|| t₂ ||Tm)
|| ex.refl A t ||Tm = refl (|| A ||Ty) (|| t ||Tm)
|| ex.jj A P t t₁ t₂ t₃ ||Tm =  jj (|| A ||Ty) (|| P ||Ty) (|| t ||Tm) (|| t₁ ||Tm) (|| t₂ ||Tm) (|| t₃ ||Tm)
|| ex.coerc S T t ||Tm = || t ||Tm

||_||Ctx : {n : ℕ} → ex.Ctx n → Ctx n
|| ex.◇ ||Ctx = ◇
|| Γ ex., A ||Ctx = || Γ ||Ctx , || A ||Ty

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
WeakenTy'CommStrip k (ex.sig A A₁) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) A₁ = refl
WeakenTy'CommStrip k ex.empty = refl
WeakenTy'CommStrip k ex.unit = refl
WeakenTy'CommStrip k ex.nat = refl
WeakenTy'CommStrip k (ex.id A u v) rewrite WeakenTy'CommStrip k A | WeakenTm'CommStrip k u | WeakenTm'CommStrip k v = refl

WeakenTm'CommStrip k (ex.var x) rewrite WeakenVar'CommStrip k x = refl
WeakenTm'CommStrip k (ex.uu i) = refl
WeakenTm'CommStrip k (ex.pi i u u₁) rewrite WeakenTm'CommStrip k u | WeakenTm'CommStrip (prev k) u₁ = refl
WeakenTm'CommStrip k (ex.lam A B u) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) B | WeakenTm'CommStrip (prev k) u = refl
WeakenTm'CommStrip k (ex.app A B u u₁) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) B | WeakenTm'CommStrip k u | WeakenTm'CommStrip k u₁ = refl
WeakenTm'CommStrip k (ex.sig i u u₁) rewrite WeakenTm'CommStrip k u | WeakenTm'CommStrip (prev k) u₁ = refl
WeakenTm'CommStrip k (ex.pair A B u u₁) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) B | WeakenTm'CommStrip k u | WeakenTm'CommStrip k u₁ = refl
WeakenTm'CommStrip k (ex.pr1 A B u) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) B | WeakenTm'CommStrip k u = refl
WeakenTm'CommStrip k (ex.pr2 A B u) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev k) B | WeakenTm'CommStrip k u = refl
WeakenTm'CommStrip k (ex.empty i) = refl
WeakenTm'CommStrip k (ex.emptyelim A u) rewrite WeakenTy'CommStrip (prev k) A | WeakenTm'CommStrip k u = refl
WeakenTm'CommStrip k (ex.unit i) = refl
WeakenTm'CommStrip k ex.tt = refl
WeakenTm'CommStrip k (ex.unitelim A u u₁) rewrite WeakenTy'CommStrip (prev k) A | WeakenTm'CommStrip k u | WeakenTm'CommStrip k u₁ = refl
WeakenTm'CommStrip k (ex.nat i) = refl
WeakenTm'CommStrip k ex.zero = refl
WeakenTm'CommStrip k (ex.suc u) = ap suc (WeakenTm'CommStrip k u)
WeakenTm'CommStrip k (ex.natelim P u u₁ u₂) rewrite WeakenTy'CommStrip (prev k) P | WeakenTm'CommStrip k u | WeakenTm'CommStrip (prev (prev k)) u₁ | WeakenTm'CommStrip k u₂ = refl
WeakenTm'CommStrip k (ex.id i u u₁ u₂) rewrite WeakenTm'CommStrip k u | WeakenTm'CommStrip k u₁ | WeakenTm'CommStrip k u₂ = refl
WeakenTm'CommStrip k (ex.refl A u) rewrite WeakenTy'CommStrip k A | WeakenTm'CommStrip k u = refl
WeakenTm'CommStrip k (ex.jj A P u u₁ u₂ u₃) rewrite WeakenTy'CommStrip k A | WeakenTy'CommStrip (prev (prev (prev k))) P | WeakenTm'CommStrip (prev k) u | WeakenTm'CommStrip k u₁ | WeakenTm'CommStrip k u₂ | WeakenTm'CommStrip k u₃ = refl
WeakenTm'CommStrip k (ex.coerc S T u) rewrite WeakenTm'CommStrip k u = {!refl!}

DerToNormal : {judg : ex.Judgment} → (ex.Derivable judg) → (Derivable (|| judg ||))
DerToNormal (ex.VarLast dj) = {!VarLast (DerToNormal dj)!}
DerToNormal (ex.VarPrev dj dj₁) = {!!}
DerToNormal (ex.VarLastCong dj) = {!!}
DerToNormal (ex.VarPrevCong dj dj₁) = {!!}
DerToNormal (ex.TySymm dj) = {!!}
DerToNormal (ex.TyTran dj dj₁ dj₂) = {!!}
DerToNormal (ex.TmSymm dj) = {!!}
DerToNormal (ex.TmTran dj dj₁ dj₂) = {!!}
DerToNormal (ex.Conv dj dj₁ dj₂) = {!!}
DerToNormal (ex.ConvEq dj dj₁ dj₂) = {!!}
DerToNormal (ex.CoercRefl dj) = {!!}
DerToNormal (ex.CoercRefl! dj) = {!!}
DerToNormal ex.UU = {!!}
DerToNormal ex.UUCong = {!!}
DerToNormal ex.UUUU = {!!}
DerToNormal ex.UUUUCong = {!!}
DerToNormal ex.ElUU= = {!!}
DerToNormal (ex.El dj) = {!!}
DerToNormal (ex.ElCong dj) = {!!}
DerToNormal (ex.Pi dj dj₁) = {!!}
DerToNormal (ex.PiCong dj dj₁ dj₂) = {!!}
DerToNormal (ex.PiUU dj dj₁) = {!!}
DerToNormal (ex.PiUUCong dj dj₁ dj₂) = {!!}
DerToNormal (ex.ElPi= dj dj₁) = {!!}
DerToNormal (ex.Lam dj dj₁ dj₂) = {!!}
DerToNormal (ex.LamCong dj dj₁ dj₂ dj₃) = {!!}
DerToNormal (ex.App dj dj₁ dj₂ dj₃) = {!!}
DerToNormal (ex.AppCong dj dj₁ dj₂ dj₃ dj₄) = {!!}
DerToNormal (ex.Sig dj dj₁) = {!!}
DerToNormal (ex.SigCong dj dj₁ dj₂) = {!!}
DerToNormal (ex.SigUU dj dj₁) = {!!}
DerToNormal (ex.SigUUCong dj dj₁ dj₂) = {!!}
DerToNormal (ex.ElSig= dj dj₁) = {!!}
DerToNormal (ex.Pair dj dj₁ dj₂ dj₃) = {!!}
DerToNormal (ex.PairCong dj dj₁ dj₂ dj₃ dj₄) = {!!}
DerToNormal (ex.Pr1 dj dj₁ dj₂) = {!!}
DerToNormal (ex.Pr1Cong dj dj₁ dj₂ dj₃) = {!!}
DerToNormal (ex.Pr2 dj dj₁ dj₂) = {!!}
DerToNormal (ex.Pr2Cong dj dj₁ dj₂ dj₃) = {!!}
DerToNormal ex.Empty = {!!}
DerToNormal ex.EmptyCong = {!!}
DerToNormal ex.EmptyUU = {!!}
DerToNormal ex.EmptyUUCong = {!!}
DerToNormal ex.ElEmpty= = {!!}
DerToNormal (ex.Emptyelim dj dj₁) = {!!}
DerToNormal (ex.EmptyelimCong dj dj₁) = {!!}
DerToNormal ex.Unit = {!!}
DerToNormal ex.UnitCong = {!!}
DerToNormal ex.UnitUU = {!!}
DerToNormal ex.UnitUUCong = {!!}
DerToNormal ex.ElUnit= = {!!}
DerToNormal ex.TT = {!!}
DerToNormal ex.TTCong = {!!}
DerToNormal (ex.Unitelim dj dj₁ dj₂) = {!!}
DerToNormal (ex.UnitelimCong dj dj₁ dj₂) = {!!}
DerToNormal ex.Nat = {!!}
DerToNormal ex.NatCong = {!!}
DerToNormal ex.NatUU = {!!}
DerToNormal ex.NatUUCong = {!!}
DerToNormal ex.ElNat= = {!!}
DerToNormal ex.Zero = {!!}
DerToNormal ex.ZeroCong = {!!}
DerToNormal (ex.Suc dj) = {!!}
DerToNormal (ex.SucCong dj) = {!!}
DerToNormal (ex.Natelim dj dj₁ dj₂ dj₃) = {!!}
DerToNormal (ex.NatelimCong dj dj₁ dj₂ dj₃ dj₄) = {!!}
DerToNormal (ex.Id dj dj₁ dj₂) = {!!}
DerToNormal (ex.IdCong dj dj₁ dj₂) = {!!}
DerToNormal (ex.IdUU dj dj₁ dj₂) = {!!}
DerToNormal (ex.IdUUCong dj dj₁ dj₂) = {!!}
DerToNormal (ex.ElId= dj dj₁ dj₂) = {!!}
DerToNormal (ex.Refl dj dj₁) = {!!}
DerToNormal (ex.ReflCong dj dj₁) = {!!}
DerToNormal (ex.JJ dj dj₁ dj₂ dj₃ dj₄ dj₅) = {!!}
DerToNormal (ex.JJCong dj dj₁ dj₂ dj₃ dj₄ dj₅ dj₆) = {!!}
DerToNormal (ex.BetaPi dj dj₁ dj₂ dj₃) = {!!}
DerToNormal (ex.BetaSig1 dj dj₁ dj₂ dj₃) = {!!}
DerToNormal (ex.BetaSig2 dj dj₁ dj₂ dj₃) = {!!}
DerToNormal (ex.BetaUnit dj dj₁) = {!!}
DerToNormal (ex.BetaNatZero dj dj₁ dj₂) = {!!}
DerToNormal (ex.BetaNatSuc dj dj₁ dj₂ dj₃) = {!!}
DerToNormal (ex.BetaIdRefl dj dj₁ dj₂ dj₃) = {!!}
DerToNormal (ex.EtaPi dj dj₁ dj₂) = {!!}
DerToNormal (ex.EtaSig dj dj₁ dj₂) = {!!}


