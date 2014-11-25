{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS -v tc.unquote:30 #-}

open import Prelude
open import Data.List
open import Builtin.Reflection as Builtin using 
  ( Arg; arg; unArg; ArgInfo; arg-info; vArg; hArg
  ; Abs; abs
  ; el; unEl
  ; Visibility; visible; hidden; instance′
  ; Relevance; relevant
  ; Name
  )
open import Integer
open import Untyped 
  using 
  ( var; con; def; lam; pi; set; unknown
  ; typeOf; shift; substTop; Context
  ; PiView; piDom; piCod; SetView) 
  renaming (Term to UTerm) public
import Tactic.Reflection.Equality
open import DerivingEq using (eqDefinition)

module Typed where

  data Term (Γ : Context) (ty : UTerm) : Set
  data Args (Γ : Context) (ty : UTerm) : UTerm → Set

  {-# TERMINATING #-}
  erase     : ∀ {Γ ty} → Term Γ ty → UTerm
  eraseArgs : ∀ {Γ ty ty'} → Args Γ ty ty' → List (Arg UTerm)

  Type : Context → Set
  Type Γ = Term Γ set

  data Term Γ ty where
    var : ∀ {ty'} (x : ty' ∈ Γ) (xs : Args Γ ty (shift (+ suc (forgetAny x)) 0 ty')) → Term Γ ty
    con : (c : Name) (xs : Args Γ ty (typeOf c)) → Term Γ ty
    def : (f : Name) (xs : Args Γ ty (typeOf f)) → Term Γ ty
    lam : {{_ : PiView ty}} → Term (unArg (piDom ty) ∷ Γ) (piCod ty) → Term Γ ty
    pi  : {{_ : SetView ty}} (a : Arg (Type Γ)) (b : Type (erase (unArg a) ∷ Γ)) → Term Γ ty
    set : {{_ : SetView ty}} → Term Γ ty
    unknown : Term Γ ty

  data Args Γ ty where
    []  : Args Γ ty ty
    _∷_ : ∀ {a b} (t : Term Γ (unArg a)) → Args Γ ty (substTop (erase t) b) → Args Γ ty (pi a b)

  erase (var i xs) = var (forgetAny i) (eraseArgs xs)
  erase (con c xs) = con c (eraseArgs xs)
  erase (def f xs) = def f (eraseArgs xs)
  erase {ty = ty} (lam t) = case piDom ty of λ { (arg (arg-info v _) _) → lam v (erase t) }
  erase (pi a b)   = pi (fmap erase a) (erase b)
  erase set        = set
  erase unknown    = unknown

  eraseArgs [] = []
  eraseArgs (_∷_ {a = arg i _} x xs) = arg i (erase x) ∷ eraseArgs xs

  compile : ∀ {Γ ty} → Term Γ ty → Builtin.Term
  compile = Untyped.compile ∘ erase
{-
  eqAny : ∀ {a b} {A : Set a} {{_ : Eq A}} {P : A → Set b} {{_ : ∀ {x} → Eq (P x)}}
          {xs} (ps qs : Any P xs) → Dec (ps ≡ qs)
  instance
    EqAny : ∀ {a b} {A : Set a} {{_ : Eq A}} {P : A → Set b} {{_ : ∀ {x} → Eq (P x)}}
            {xs : List A} → Eq (Any P xs)
    EqAny = record{ _==_ = eqAny }  

  unquoteDef eqAny = eqDefinition (quote Any)

  eqId : ∀ {a} {A : Set a} {{_ : Eq A}} {x y : A} (e₁ e₂ : x ≡ y) → Dec (e₁ ≡ e₂)
  instance
    EqId : ∀ {a} {A : Set a} {{_ : Eq A}} {x y : A} → Eq (x ≡ y)
    EqId = record { _==_ = eqId }
  unquoteDef eqId = eqDefinition (quote _≡_)
        
  {-# TERMINATING #-}
  eqTerm : ∀ {Γ ty} (t₁ t₂ : Term Γ ty) → Dec (t₁ ≡ t₂)
  instance
    EqTerm : ∀ {Γ ty} → Eq (Term Γ ty)
    EqTerm = record{ _==_ = eqTerm }
  unquoteDef eqTerm = eqDefinition (quote Term)
  -}



