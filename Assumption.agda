open import Prelude
open import Prelude.Equality
open import Integer
open import Data.List
open import Untyped using (Context; shift)
open import Typed

module Assumption where

  HasAssumption : (depth : Nat) (Γ : Context) (ty : Untyped.Term) → Set
  HasAssumption d [] ty = ⊥
  HasAssumption d (x ∷ Γ) ty = 
    case ty == shift (+ suc d) 0 x of (λ { 
      (yes _) → ⊤ ; 
      (no _)  → HasAssumption (suc d) Γ ty })

  getAssumptionType : ∀ d Γ ty → {_ : HasAssumption d Γ ty} → Untyped.Term
  getAssumptionType d [] ty {}
  getAssumptionType d (x ∷ Γ) ty with ty == shift (+ suc d) 0 x
  getAssumptionType d (x ∷ Γ) ty | yes _ = x
  getAssumptionType d (x ∷ Γ) ty | no _  = λ {h} → getAssumptionType (suc d) Γ ty {h} 

  getAssumptionIndex : ∀ d Γ ty → {h : HasAssumption d Γ ty} → getAssumptionType d Γ ty {h} ∈ Γ
  getAssumptionIndex d [] ty {}
  getAssumptionIndex d (x ∷ Γ) ty with ty == shift (+ suc d) 0 x
  getAssumptionIndex d (x ∷ Γ) ._ | yes refl = zero!
  getAssumptionIndex d (x ∷ Γ) ty | no _     = λ {h} → suc (getAssumptionIndex (suc d) Γ ty {h})

  getAssumption : ∀ d Γ ty → {h : HasAssumption d Γ ty} → 
                  ty ≡ (shift (+ suc (d + forgetAny (getAssumptionIndex d Γ ty {h}))) 0 (getAssumptionType d Γ ty {h}))
  getAssumption d [] ty {}
  getAssumption d (x ∷ Γ) ty with ty == shift (+ suc d) 0 x
  getAssumption d (x ∷ Γ) ._ | yes refl = cong (λ n → shift (+ suc n) 0 x) (+zero d)
    where
      +zero : ∀ m → m ≡ m + zero
      +zero zero = refl
      +zero (suc m) = cong suc (+zero m)
  getAssumption d (x ∷ Γ) ty | no _     = λ {h} → 
    trans (getAssumption (suc d) Γ ty {h}) 
          (cong (λ n → shift (+ suc n) 0 (getAssumptionType (suc d) Γ ty {h})) 
                (+suc d)) 
    where
      +suc : ∀ m {n} → suc (m + n) ≡ m + (suc n)
      +suc zero = refl
      +suc (suc m) = cong suc (+suc m)

  assumption : ∀ {Γ ty} {h : HasAssumption 0 Γ ty} → Term Γ ty
  assumption {Γ = Γ} {ty = ty} {h = h} = 
    var (getAssumptionIndex 0 Γ ty {h}) 
        (transport (Args Γ ty) (getAssumption 0 Γ ty {h}) [])

  module _ where

    open import Ttac

    test : ∀ {k l m} → Vec Nat k → Vec Nat l → Vec Nat m → Vec Nat l
    test x y z = tactic ttac 
                 assumption
