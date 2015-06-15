module Search where

open import Prelude hiding (id)
open import Integer
open import Data.List
open import Builtin.Reflection using (vArg; hArg)
open import Untyped
  using
  ( var; con; def; lam; pi; set; unknown
  ; typeOf; shift; substTop
  ; PiView; piInfo; piDom; piCod; SetView; DefView; defName
  ; id; wk; sub; lift)
  renaming (Context to UContext)
  renaming (Term to UTerm)
  renaming (EqTerm to EqUTerm)
open import UntypedEquality
open import Typed
open import Reduce using (normalize; Normal)
open import Ttac
open import Typecheck

data MyList : Set where
  nil  : MyList
  cons : Nat → MyList → MyList

data MyEl : (n : Nat) → MyList → Set where
  here : (x : Nat) (xs : MyList) → MyEl x (cons x xs)
  there : (x y : Nat) (xs : MyList) → MyEl x xs → MyEl x (cons y xs)

piNotList : ∀ s {{_ : PiView s}} → ¬ (EquivTerm s (def (quote MyList) []))
piNotList ._ {{}} (cong-def x₁)
piNotList ._ {{}} (beta₁ eq)
piNotList s (beta₂ {t = t} {{}} _)



mysearch : ∀ {Γ} → (x : Term Γ (def (quote Nat) [])) (xs : Term Γ (def (quote MyList) [])) →
           Maybe (Term Γ (def (quote MyEl) (vArg (erase x) ∷ vArg (erase xs) ∷ [])))
mysearch x (con c xs) with c == quote cons
mysearch x (con .(quote cons) ([] {{eq}})) | yes refl = ⊥-elim (piNotList _ eq)
mysearch x (con .(quote cons) (_∷_ {b = ._} {{cong-pi eq₁ (cong-pi x₁ eq₂)}} t [])) | yes refl = {!!}
mysearch x (con .(quote cons) (_∷_ {b = ._} {{cong-pi eq₁ (beta₁ eq₂)}} t [])) | yes refl = {!!}
mysearch x (con .(quote cons) (_∷_ {b = b} {{cong-pi eq₁ eq₂}} x' (xs ∷ []))) | yes refl = {!x₁!} {-with x == x'
mysearch x (con ._ (.x ∷ (xs ∷ [] {{refl}}))) | yes refl | yes refl =
  just (con (quote here) (x ∷ xs ∷ []))
mysearch x (con ._ (x' ∷ (xs ∷ [] {{refl}}))) | yes refl | no _ =
  case (mysearch x xs) of λ
    { (just pos) → just (con (quote there) (x ∷ x' ∷ xs ∷ pos ∷ []))
    ; nothing    → nothing
    }-}
mysearch x (con .(quote cons) (_∷_ {{cong-pi x₁ x₂}} x' (xs ∷ bad))) | yes refl = {!!}
mysearch x (con c xs) | no _ = nothing
mysearch x xs = nothing

test : MyEl 1 (cons 0 (cons 2 (cons 1 (cons 4 nil))))
test = tactic ttac (fromJust (mysearch (con (quote Nat.suc) (con (quote Nat.zero) []′ ∷ [])) {!!}))


{-


pattern `List A = def (quote List) (hArg (unknown / id) ∷ vArg (A / id) ∷ [])

pattern _`∈_ x xs = def (quote Data.List._∈_) (hArg (unknown / id) ∷ hArg (unknown / id) ∷ vArg (x / id) ∷ vArg (xs / id) ∷ [])

cases : ∀ {a b} {A : Set a} {B : Set b} {{_ : Eq A}} →
        (x : A) → List (A × B) → B → B
cases x₁ [] default = default
cases x₁ ((x₂ , y) ∷ cs) default with x₁ == x₂
cases x₁ ((.x₁ , y) ∷ cs) default | yes refl = y
cases x₁ (( x₂ , y) ∷ cs) default | no  _    = cases x₁ cs default

search : ∀ {Γ A} → (x : Term Γ A) (xs : Term Γ (`List A)) → Maybe (Term Γ (erase x `∈ erase xs))
search x (con c xs) with c == quote List._∷_
search x (con ._ (unknown ∷ ty ∷ rest)) | yes refl = {!rest!} {-with x == x'
search x (con ._ (unknown ∷′ ty ∷′ .x ∷′ xs ∷′ []′)) | yes refl | yes refl =
  just (con (quote Any.zero) (? ∷ ? ∷ {!!} ∷ {!!} ∷ {!!} ∷ {!!} ∷ {!!} ∷ {![]!}))
search x (con ._ (unknown ∷′ ty ∷′ x' ∷′ xs ∷′ []′)) | yes refl | no  _  = {!!} -}
search x (con ._ _) | yes refl = {!!}
search x (con c xs) | no  _    = {!!}
{-search x₁ (con ._ (_ ∷ _ ∷ x ∷ xs ∷ _)) | yes refl with (erase x) == (erase x₁)
search x₁ (con ._ (t ∷ (t₁ ∷ (x ∷ (xs ∷ x₃))))) | yes refl | yes eq = {!!}
search x₁ (con ._ (t ∷ (t₁ ∷ (x ∷ (xs ∷ x₃))))) | yes refl | no  _  = {!!}
search x₁ (con c xs) | no x = nothing-}
search x _ = nothing

-}
