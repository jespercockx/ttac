{-# OPTIONS -v tc.unquote:30 #-}

open import Prelude hiding (id; [_])
open import Builtin.Reflection as Builtin using
  ( Arg; arg; unArg; ArgInfo; arg-info; vArg; hArg
  ; Abs; abs
  ; el; unEl
  ; Visibility; visible; hidden; instance′
  ; Relevance; relevant
  ; Name
  )
open import Untyped
  using
  ( var; con; def; lam; pi; set; unknown
  ; typeOf; shift; substTop
  ; PiView; piInfo; piDom; piCod; SetView
  ; Context; ∅; _,_)
  renaming (Term to UTerm; Args to UArgs)
  renaming (EqTerm to EqUTerm)
open import UntypedEquality
open import Typed
open import Reduce using (normalize; Normal)

module Typecheck where


mutual
  ⊢_ : Context → Set
  ⊢ ∅ = ⊤
  ⊢ (Γ , ty) = (⊢ Γ) × (Γ ⊢ ty ∶ set)

  _⊢_∶_ : Context → UTerm → UTerm → Set
  Γ ⊢ t ∶ ty = Σ (Term Γ ty) (λ tc → erase tc ≡ t)

  _⊢_∶_⇒_ : Context → List (Arg UTerm) → UTerm → UTerm → Set
  Γ ⊢ ts ∶ ty ⇒ ty' = Σ (Args Γ ty ty') (λ tsc → eraseArgs tsc ≡ ts)

data Error : Set where
  VariableOutOfScope : Context → Nat → Error
  VisibilityMismatch : Error
  ArgInfoMismatch : Error
  ShouldBePi : UTerm → Error
  TypeMismatch : UTerm → UTerm → Error
  TypeError : UTerm → Error
  NotSupported : String → Error

lookupVar : (Γ : Context) (d i : Nat) →
            Maybe (Σ UTerm (λ ty → Σ (ShiftedInCtx d ty Γ) (λ p → erase∈ p ≡ i)))
lookupVar ∅ d i = nothing
lookupVar (Γ , ty) d zero = just (_ , (zero , refl))
lookupVar (Γ , ty) d (suc i) =
  case (lookupVar Γ (suc d) i) of λ
    { (just (ty , (p , e))) → just (ty , (suc p , cong suc e))
    ; nothing               → nothing
    }

{-# TERMINATING #-}
typeCheck : (Γ : Context) (t : UTerm) (ty : UTerm) →
            Either Error (Γ ⊢ t ∶ ty)

typeInfer : (Γ : Context) (t : UTerm) →
            Either Error (Σ UTerm (λ ty → Γ ⊢ t ∶ ty))

checkArgs : (Γ : Context) (ts : UArgs) (ty : UTerm) →
            Either Error (Σ UTerm (λ ty' → Γ ⊢ ts ∶ ty ⇒ ty'))

typeCheck Γ (lam v t) (pi (arg (arg-info v' _) a) b) with v == v'
typeCheck Γ (lam v t) (pi (arg (arg-info .v _) a) b) | yes refl =
  case (typeCheck Γ a set) of λ
    { (left err)        → left err
    ; (right (a' , ea)) →
        case (typeCheck (Γ , erase a') t b) of λ
          { (left err)      → left err
          ; (right (t , e)) → right (lam a'
                {{cong-pi (refl , transport (EquivTerm (erase a')) ea equiv-refl) equiv-refl}}
              t , cong (lam v) e)
          }
    }
typeCheck Γ (lam v t) (pi (arg (arg-info v' _) a) b) | no x = left VisibilityMismatch
typeCheck Γ (lam v t) ty = left (ShouldBePi ty)

typeCheck Γ t ty =
  case (typeInfer Γ t) of λ
    { (left err) → left err
    ; (right (ty' , (t' , e))) →
        case (ty' == ty) of λ
          { (yes eq) → right (transport (_⊢_∶_ Γ t) eq (t' , e))
          ; (no _)   → left (TypeMismatch ty ty')
          }
    }

typeInfer Γ (var x args) =
  case (lookupVar Γ 0 x) of λ
    { (just (ty , (p , e))) →
        case (checkArgs Γ args ty) of λ
          { (left err)                  → left err
          ; (right (ty' , (args , es))) → right (ty' , (var p args , cong₂ var e es))
          }
    ; nothing               → left (VariableOutOfScope Γ x)
    }

typeInfer Γ (con c args) =
  case (checkArgs Γ args (typeOf c)) of λ
    { (left err)                 → left err
    ; (right (ty , (args , es))) → right (ty , (con c args , cong (con c) es))
    }

typeInfer Γ (def f args) =
  case (checkArgs Γ args (typeOf f)) of λ
    { (left err)                 → left err
    ; (right (ty , (args , es))) → right (ty , (def f args , cong (def f) es))
    }

typeInfer Γ (pi (arg i a) b) =
  case (typeCheck Γ a set) of λ
    { (left err) → left err
    ; (right (a , ea)) →
        case (typeCheck (Γ , erase a) b set) of λ
        { (left err)       → left err
        ; (right (b , eb)) → right (set , (pi (arg i a) b , cong₂ pi (cong (arg i) ea) eb))
        }
    }

typeInfer Γ set = right (set , (set , refl))


typeInfer Γ t = left (TypeError t)

checkArgs Γ [] ty = right (ty , ([] {{equiv-refl}} , refl))
checkArgs Γ (arg i t ∷ ts) (pi (arg i' a) b) =
  case (i' == i) of λ
    { (yes ei) →
        case (typeCheck Γ t a) of λ
          { (left err)       → left err
          ; (right (t' , e)) →
              case (checkArgs Γ ts (substTop (erase t') b)) of λ
                { (left err)                 → left err
                ; (right (ty' , (ts' , es))) → right (ty' , ((t' ∷′ ts') , cong₂ _∷_ (cong₂ arg ei e) es))
                }
          }
    ; (no _)   → left ArgInfoMismatch
    }
checkArgs Γ (x ∷ ts) ty = left (ShouldBePi ty)

checkContext : (Γ : Context) → Either Error (⊢ Γ)
checkContext ∅ = right tt
checkContext (Γ , ty) =
  case (checkContext Γ) of λ
    { (left err) → left err
    ; (right ⊢Γ) →
        case (typeCheck Γ ty set) of λ
          { (left err)       → left err
          ; (right Γ⊢ty∶set) → right (⊢Γ , Γ⊢ty∶set)
          }
    }

checkConstantType : (c : Name) → ∀ {Γ} → Γ ⊢ typeOf c ∶ set
checkConstantType c {Γ} =
  case (typeCheck Γ (typeOf c) set) of λ
    { (left err)          → IMPOSSIBLE
    ; (right checkedType) → checkedType
    }
  where
    postulate IMPOSSIBLE : _


private

  FromEither : {A B : Set} → Either A B → Set
  FromEither {A = A} (left _)  = A
  FromEither {B = B} (right _) = B

  fromEither : {A B : Set} (x : Either A B) → FromEither x
  fromEither (left x)  = x
  fromEither (right x) = x

  test = fromEither (typeInfer ∅ (def (quote transport) (hArg (def (quote lzero) []) ∷ hArg (def (quote lzero) []) ∷ [])))

  tester : {A : Set} (B : A → Set) {x y : A} → x ≡ y → B x → B y
  tester = unquote (compile (fst (snd test)))
