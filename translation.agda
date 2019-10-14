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
WeakenTy'CommStrip : {n : ℕ} → (k : Fin (suc n)) → (A : ex.TyExpr n) → || ex.weakenTy' k A ||Ty ≡ weakenTy' k (|| A ||Ty)
WeakenTm'CommStrip : {n : ℕ} → (k : Fin (suc n)) → (u : ex.TmExpr n) → || ex.weakenTm' k u ||Tm ≡ weakenTm' k (|| u ||Tm)

WeakenTy'CommStrip k A = {!!}

WeakenTm'CommStrip k u = {!!}

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


