module Untyped where

open import Prelude
open import Data.List
open import Builtin.Reflection as Builtin using 
  ( Arg; arg; unArg; ArgInfo; arg-info; vArg; hArg
  ; Abs; abs
  ; el; unEl
  ; Visibility; visible; hidden; instance′
  ; Relevance; relevant
  ; Name
  ) public
open import Tactic.Deriving.Eq
import Tactic.Reflection.Equality

open import Integer
  
private 
  postulate 
    error          : ∀ {a} {A : Set a} → String → A
    notImplemented : ∀ {a} {A : Set a} → String → A

data Term : Set where
  var : (i : Nat)  (args : List (Arg Term)) → Term
  con : (c : Name) (args : List (Arg Term)) → Term
  def : (f : Name) (args : List (Arg Term)) → Term
  lam : (v : Visibility) (t : Term) → Term
  pi  : (a : Arg Term) (b : Term) → Term
  set : Term
  unknown : Term

PiView : Term → Set 
PiView (pi a b) = ⊤
PiView _        = ⊥

piDom : ∀ t {{_ : PiView t}} → Arg Term
piDom (var _ _) {{()}}
piDom (con _ _) {{()}}
piDom (def _ _) {{()}}
piDom (lam _ _) {{()}}
piDom (pi a b)  {{tt}} = a
piDom (set)     {{()}}
piDom (unknown) {{()}}

piCod : ∀ t → {{_ : PiView t}} → Term
piCod (var _ _) {{()}}
piCod (con _ _) {{()}}
piCod (def _ _) {{()}}
piCod (lam _ _) {{()}}
piCod (pi a b)  {{tt}} = b
piCod (set)     {{()}}
piCod (unknown) {{()}}

SetView : Term → Set 
SetView set = ⊤
SetView _   = ⊥

Context : Set
Context = List Term

lookupDBI : (Γ : Context) (i : Nat) → Maybe (Σ Term λ x → Σ (x ∈ Γ) λ p → forgetAny p ≡ i)
lookupDBI [] i = nothing
lookupDBI (x ∷ xs) zero = just (x , zero! , refl)
lookupDBI (x ∷ xs) (suc i) with lookupDBI xs i
lookupDBI (x ∷ xs) (suc i) | nothing = nothing
lookupDBI (x ∷ xs) (suc i) | just (y , p , e) = just (y , suc p , cong suc e)
  
{-# TERMINATING #-}
parse : Builtin.Term → Term
parse (Builtin.var i args) = var i (map (fmap parse) args)
parse (Builtin.con c args) = con c (map (fmap parse) args)
parse (Builtin.def f args) = def f (map (fmap parse) args)
parse (Builtin.lam v (abs _ t)) = lam v (parse t)
parse (Builtin.pi a (abs _ b)) = pi (fmap (parse ∘ unEl) a) (parse (unEl b))
parse (Builtin.sort s) = set
parse (Builtin.lit (Builtin.nat zero)) = con (quote Nat.zero) []
parse (Builtin.lit (Builtin.nat (suc n))) = con (quote Nat.suc) (vArg (parse (Builtin.lit (Builtin.nat n))) ∷ [])
{-# CATCHALL #-}
parse _ = unknown

{-# TERMINATING #-}
compile : Term → Builtin.Term
compile (var i args) = Builtin.var i (map (fmap compile) args)
compile (con c args) = Builtin.con c (map (fmap compile) args)
compile (def f args) = Builtin.def f (map (fmap compile) args)
compile (lam v t) = Builtin.lam v (abs "" (compile t))
compile (pi a b) = Builtin.pi (fmap (el Builtin.unknown ∘ compile) a) (abs "" (el Builtin.unknown (compile b)))
compile set = Builtin.sort Builtin.unknown
compile unknown = Builtin.unknown

typeOf : Name → Term
typeOf = parse ∘ unEl ∘ Builtin.typeOf

{-# TERMINATING #-}
shift : (n : Int) (cutoff : Nat) → Term → Term
  
shiftArgs : (n : Int) (cutoff : Nat) → List (Arg Term) → List (Arg Term)
shiftArgs n cutoff = map (fmap (shift n cutoff))

shift n cutoff (var i args) = 
  if (i ≥ cutoff) 
  then (case (n +I + i) of λ { 
    (+   i') → var i' (shiftArgs n cutoff args) ; 
    -[1+ _ ] → error "negative De Bruijn index" })
  else var i (shiftArgs n cutoff args) 
shift n cutoff (con c args) = con c (shiftArgs n cutoff args)
shift n cutoff (def f args) = def f (shiftArgs n cutoff args)
shift n cutoff (lam v x)    = lam v (shift n (suc cutoff) x)
shift n cutoff (pi a b)     = pi (fmap (shift n cutoff) a) (shift n (suc cutoff) b)
shift n cutoff set          = set
shift n cutoff unknown      = unknown

{-# TERMINATING #-}
apply : Term → List (Arg Term) → Term
subst : (n : Nat) (s : Term) → Term → Term

substTop : Term → Term → Term
substTop s = shift -1 0 ∘ subst 0 (shift +1 0 s)

substArgs : (n : Nat) (s : Term) → List (Arg Term) → List (Arg Term)
substArgs n s = map (fmap (subst n s))

substArgsTop : Term → List (Arg Term) → List (Arg Term)
substArgsTop s = map (fmap (substTop s)) 

apply (var i args) xs       = var i (args ++ xs)
apply (con c args) xs       = con c (args ++ xs)
apply (def f args) xs       = def f (args ++ xs)
apply (lam v t)    []       = lam v t
apply (lam v t)    (x ∷ xs) = apply (substTop (unArg x) t) xs
apply (pi a b)     []       = pi a b
apply (pi a b)     (x ∷ xs) = error "a pi is not a function"
apply set          []       = set
apply set          (x ∷ xs) = error "set is not a function"
apply unknown      xs       = unknown

subst n s (var i args) = 
  if (eqNat n i) 
  then apply s (substArgs n s args) 
  else var   i (substArgs n s args)
subst n s (con c args) = con c (substArgs n s args)
subst n s (def f args) = def f (substArgs n s args)
subst n s (lam v t)    = lam v (subst (suc n) (shift +1 0 s) t)
subst n s (pi a b)     = pi (fmap (subst n s) a) (subst (suc n) (shift +1 0 s) b)
subst n s set          = set
subst n s unknown      = unknown

piApply : Term → List (Arg Term) → Term
piApply t []       = t
piApply (pi a b) (x ∷ xs) = piApply (substTop (unArg x) b) xs
{-# CATCHALL #-}
piApply _ (x ∷ xs) = error "not enough pie"

instance
  {-# TERMINATING #-}
  EqTerm : Eq Term
  EqTerm = record{ _==_ = eqTerm }
    where
      eqTerm : (t₁ t₂ : Term) → Dec (t₁ ≡ t₂)
      unquoteDef eqTerm = deriveEqDef (quote Term) (quote eqTerm)

