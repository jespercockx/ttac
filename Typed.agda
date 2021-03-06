{-# OPTIONS --no-positivity-check #-}

open import Prelude
open import Data.List using (Any; forgetAny) renaming (_∈_ to _l∈_)
open import Builtin.Reflection as Builtin using
  ( Arg; arg; unArg; ArgInfo; arg-info; vArg; hArg
  ; Abs; abs
  ; el; unEl
  ; Visibility; visible; hidden; instance′
  ; Relevance; relevant
  ; Name
  )
open import Tactic.Reflection.Telescope using (telView)
open import Integer
open import Untyped
  using
  ( var; con; def; lam; pi; set; unknown
  ; typeOf; shift; substTop
  ; Context; ∅; _,_
  ; PiView; piInfo; piDom; piCod; SetView)
  renaming (Term to UTerm)
  renaming (EqTerm to EqUTerm)
open import UntypedEquality
import Tactic.Reflection.Equality
open import Tactic.Deriving.Eq

module Typed where

  data ShiftedInCtx (d : Nat) : UTerm → Context → Set
  Type : Context → Set
  data Term (Γ : Context) (ty : UTerm) : Set
  data Args (Γ : Context) (ty ty' : UTerm) : Set

  {-# TERMINATING #-}
  erase     : ∀ {Γ ty} → Term Γ ty → UTerm
  eraseArgs : ∀ {Γ ty ty'} → Args Γ ty ty' → List (Arg UTerm)

  Type Γ = Term Γ set

  data ShiftedInCtx d where
    zero : ∀ {ty Γ} → ShiftedInCtx d (shift (suc d) 0 ty) (Γ , ty)
    suc  : ∀ {ty ty' Γ} → ShiftedInCtx (suc d) ty Γ → ShiftedInCtx d ty (Γ , ty')

  _∈_ : UTerm → Context → Set
  ty ∈ Γ = ShiftedInCtx 0 ty Γ

  erase∈ : ∀ {d ty Γ} → ShiftedInCtx d ty Γ → Nat
  erase∈ zero = zero
  erase∈ (suc loc) = suc (erase∈ loc)

  data Term Γ ty where
    var : ∀ {ty'} (x : ty' ∈ Γ) (xs : Args Γ ty' ty) → Term Γ ty
    con : (c : Name) (xs : Args Γ (typeOf c) ty) → Term Γ ty
    def : (f : Name) (xs : Args Γ (typeOf f) ty) → Term Γ ty
    lam : (dom : Type Γ) {i : ArgInfo} {cod : UTerm}
          {{_ : EquivTerm (pi (arg i (erase dom)) cod) ty}} →
          Term (Γ , erase dom) cod → Term Γ ty
    pi  : {{_ : EquivTerm set ty}} (a : Arg (Type Γ)) (b : Type (Γ , erase (unArg a))) → Term Γ ty
    set : {{_ : EquivTerm set ty}} → Term Γ ty
    unknown : Term Γ ty

  lam′ : ∀ {Γ} (dom : Type Γ) {i : ArgInfo} {cod : UTerm} →
         Term (Γ , erase dom) cod → Term Γ (pi (arg i (erase dom)) cod)
  lam′ dom = lam dom {{equiv-refl}}

  infixr 5 _∷_
  data Args Γ ty ty' where
    []  : {{_ : EquivTerm ty ty'}} → Args Γ ty ty'
    _∷_ : ∀ {a b} {{_ : EquivTerm (pi a b) ty}}
          (t : Term Γ (unArg a)) →
          Args Γ (substTop (erase t) b) ty' →
          Args Γ ty ty'

  []′ : ∀ {Γ ty} → Args Γ ty ty
  []′ = [] {{equiv-refl}}

  infixr 5 _∷′_
  _∷′_ : ∀ {Γ a b ty} (t : Term Γ (unArg a)) → Args Γ (substTop (erase t) b) ty → Args Γ (pi a b) ty
  _∷′_ = _∷_ {{equiv-refl}}

  erase (var i xs) = var (erase∈ i) (eraseArgs xs)
  erase (con c xs) = con c (eraseArgs xs)
  erase (def f xs) = def f (eraseArgs xs)
  erase (lam _ {arg-info v _} t)  = lam v (erase t)
  erase (pi a b)   = pi (fmap erase a) (erase b)
  erase set        = set
  erase unknown    = unknown

  eraseArgs [] = []
  eraseArgs (_∷_ {arg i _} x xs) = arg i (erase x) ∷ eraseArgs xs

  parseCtx : List (Arg Builtin.Type) → Context
  parseCtx [] = ∅
  parseCtx (x ∷ Γ) = parseCtx Γ , Untyped.parse (unEl (unArg x))

  compile : ∀ {Γ ty} → Term Γ ty → Builtin.Term
  compile = Untyped.compile ∘ erase

  {-# TERMINATING #-}
  eqTerm : ∀ {Γ ty} (t₁ t₂ : Term Γ ty) → Dec (t₁ ≡ t₂)
  eqArgs : ∀ {Γ ty ty'} (xs₁ xs₂ : Args Γ ty ty') → Dec (xs₁ ≡ xs₂)

  eqContext : (Γ₁ Γ₂ : Context) → Dec (Γ₁ ≡ Γ₂)
  eqShiftedInCtx : ∀ {d ty Γ} (p q : ShiftedInCtx d ty Γ) → Dec (p ≡ q)

  instance
    EqTerm : ∀ {Γ ty} → Eq (Term Γ ty)
    EqTerm = record{ _==_ = eqTerm }

    EqArgs : ∀ {Γ ty ty'} → Eq (Args Γ ty ty')
    EqArgs = record{ _==_ = eqArgs }

    EqContext : Eq Context
    EqContext = record{ _==_ = eqContext }

    EqShiftedInCtx : ∀ {d ty Γ} → Eq (ShiftedInCtx d ty Γ)
    EqShiftedInCtx = record{ _==_ = eqShiftedInCtx }

  unquoteDef eqTerm = deriveEqDef (quote Term)
  unquoteDef eqArgs = deriveEqDef (quote Args)
  unquoteDef eqContext = deriveEqDef (quote Context)

  eqShiftedInCtx zero zero = yes refl
  eqShiftedInCtx zero (suc q) = no λ ()
  eqShiftedInCtx (suc p) zero = no λ ()
  eqShiftedInCtx (suc p) (suc q) with p == q
  eqShiftedInCtx (suc p) (suc .p) | yes refl = yes refl
  eqShiftedInCtx (suc p) (suc q)  | no  neq  = no λ eq → neq (aux eq)
    where
      aux : ∀ {d ty₁ ty₂ Γ p r} → ShiftedInCtx.suc {d} {ty₁} {ty₂} {Γ} p ≡ ShiftedInCtx.suc {d} {ty₁} {ty₂} {Γ} r → p ≡ r
      aux refl = refl

