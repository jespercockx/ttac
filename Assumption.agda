open import Prelude
open import Integer
open import Data.List hiding (_∈_)
open import Untyped using (shift; Context; ∅; _,_)
open import UntypedEquality
open import Typed

-- general stuff for Prelude.Decidable
module _ where
  IsYes : ∀ {l} {P : Set l} → Dec P → Set
  IsYes (yes _) = ⊤
  IsYes (no _) = ⊥

  fromYes : ∀ {l} {P : Set l} → (dec : Dec P) → {{isYes : IsYes dec}} → P
  fromYes (yes p) = p
  fromYes (no _) {{}}

  stepDec : ∀ {p p′} {P : Set p} {P′ : Set p′} →
            (P → P′) → (¬ P → ¬ P′) → Dec P → Dec P′
  stepDec P⇒P′ ¬P⇒¬P′ (yes p) = yes (P⇒P′ p)
  stepDec P⇒P′ ¬P⇒¬P′ (no ¬p) = no (¬P⇒¬P′ ¬p)

module Assumption where
  notSuc : ∀ {d ty Γ x} →
                (ty ≡ shift (suc d) 0 x → ⊥) →
                (ShiftedInCtx (suc d) ty Γ → ⊥) → ShiftedInCtx d ty (Γ , x) → ⊥
  notSuc notHere _ zero with notHere refl
  notSuc notHere _ zero | ()
  notSuc _ notThere (suc loc) with notThere loc
  notSuc _ notThere (suc loc) | ()

  _∈?_ : (ty : Untyped.Term) (Γ : Context) → Dec (ty ∈ Γ)
  ty ∈? Γ = go 0 Γ ty
    where go : (d : Nat) → (Γ : Context) → (ty : Untyped.Term) → Dec (ShiftedInCtx d ty Γ)
          go d ∅ ty = no (λ ())
          go d (Γ , x) ty with ty == shift (suc d) 0 x
          go d (Γ , x) ._ | yes refl = yes zero
          go d (Γ , x) ty | no notHere = stepDec suc (notSuc notHere) (go (suc d) Γ ty)

  assumption : ∀ {Γ ty} {h : IsYes (ty ∈? Γ)} → Term Γ ty
  assumption {Γ = Γ} {ty = ty} = var (fromYes (ty ∈? Γ)) ([] {{equiv-refl}})

module Test where

  open Assumption
  open import Ttac

  foox : (x : Nat) (y : Bool → Bool) (z : Vec Nat 3) → Nat
  foox x y z = tactic ttac assumption

  fooy : (x : Nat) (y : Bool → Bool) (z : Vec Nat 3) → Bool → Bool
  fooy x y z = tactic ttac assumption

  fooz : (x : Nat) (y : Bool → Bool) (z : (λ x → Vec Nat (1 + x)) 2) → Vec Nat (2 + 1)
  fooz x y z = tactic ttac assumption
