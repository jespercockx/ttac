{-# OPTIONS -v tc.unquote.def:30 #-}
module Untyped where

open import Prelude hiding (id; [_]; _$_; _!_)
open import Builtin.Reflection as Builtin using
  ( Arg; arg; unArg; ArgInfo; arg-info; vArg; hArg
  ; Abs; abs
  ; el; unEl
  ; Visibility; visible; hidden; instance′
  ; Relevance; relevant
  ; Name
  )
open import Tactic.Deriving.Eq
open import Builtin.Reflection using (definitionOf)

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

infixl 1 _,_
data Context : Set where
  ∅ : Context
  _,_ : (Γ : Context) → Term → Context

data Substitution : Set where
  id    : Substitution
  wk    : Nat → Substitution → Substitution
  sub   : Term → Substitution → Substitution
  lift  : Nat → Substitution → Substitution

private
  weakenS : Nat → Substitution → Substitution
  weakenS 0 σ = σ
  weakenS n (wk k σ) = wk (n + k) σ
  weakenS n σ = wk n σ

  raise : Nat → Substitution
  raise n = weakenS n id

  liftS : Nat → Substitution → Substitution
  liftS 0 σ = σ
  liftS n id = id
  liftS n (lift k σ) = lift (n + k) σ
  liftS n σ = lift n σ

  raiseFrom : (n : Nat) (cutoff : Nat) → Substitution
  raiseFrom n cutoff = liftS cutoff (raise n)

  dropS : Nat → Substitution → Substitution
  dropS 0 σ = σ
  dropS (suc n) (sub t σ) = dropS n σ
  dropS n id = raise n
  dropS n (wk k σ) = weakenS k (dropS n σ)
  dropS n (lift k σ) = case (compare n k) of λ
    { (less    (diff d _)) → weakenS n (liftS d σ)
    ; (equal   _         ) → weakenS n σ
    ; (greater (diff d _)) → weakenS k (dropS d σ)
    }

  subS : Term → Substitution → Substitution
  subS (var k []) (wk (suc n) σ) =
    if isYes (k == n)
    then weakenS n (liftS 1 σ)
    else sub (var k []) (weakenS (suc n) σ)
  subS t σ = sub t σ

Args = List (Arg Term)

record Subst (T : Set) : Set where
  field applySubst : Substitution → T → T

  _[_] : T → Substitution → T
  _[_] = flip applySubst

open Subst {{...}} public

{-# TERMINATING #-}
_!_ : Substitution → Nat → Term
_◂_ : Substitution → Substitution → Substitution
_$_ : Term → Args → Term

instance SubstTerm : Subst Term
instance SubstArg : {T : Set} {{_ : Subst T}} → Subst (Arg T)
instance SubstList : {T : Set} {{_ : Subst T}} → Subst (List T)

SubstTerm = record { applySubst = subst }
  where
    subst : Substitution → Term → Term
    subst id t = t
    subst σ (var i args) = (σ ! i) $ (args [ σ ])
    subst σ (con c args) = con c (args [ σ ])
    subst σ (def f args) = def f (args [ σ ])
    subst σ (lam v t)    = lam v (t [ liftS 1 σ ])
    subst σ (pi a b)     = pi (a [ σ ]) (b [ liftS 1 σ ])
    subst σ set          = set
    subst σ unknown      = unknown

SubstArg {T} = record { applySubst = subst }
  where
    subst : Substitution → Arg T → Arg T
    subst σ = fmap (applySubst σ)

SubstList {T} = record { applySubst = subst }
  where
    subst : Substitution → List T → List T
    subst σ = map (applySubst σ)

id        ! i     = var i []
wk   n id ! i     = var (i + n) []
wk   n σ  ! i     = (σ ! i) [ raise n ]
sub  t σ  ! zero  = t
sub  t σ  ! suc i = σ ! i
lift n σ  ! i     = case compare i n of λ
  { (less (diff k _))    → var i []
  ; (equal p)            → (σ ! 0)     [ raise n ]
  ; (greater (diff d _)) → (σ ! suc d) [ raise n ]
  }

id             ◂ τ  = τ
σ              ◂ id = σ
wk   k       σ ◂ τ  = σ ◂ dropS k τ
sub  t       σ ◂ τ  = subS (t [ τ ]) (σ ◂ τ)
lift zero    σ ◂ τ  = σ ◂ τ
lift (suc k) σ ◂ τ  = subS (τ ! 0) (weakenS 1 (liftS k σ) ◂ τ)

shift : {T : Set} {{_ : Subst T}}
        (n : Nat) (cutoff : Nat) → T → T
shift n cutoff t = t [ raiseFrom n cutoff ]

subst : {T : Set} {{_ : Subst T}}
        (n : Nat) (s : Term) → T → T
subst n s t = t [ liftS n (subS s id) ]

substTop : {T : Set} {{_ : Subst T}}
           (t : Term) → T → T
substTop = subst 0

f            $ []       = f
(var i args) $ xs       = var i (args ++ xs)
(con c args) $ xs       = con c (args ++ xs)
(def f args) $ xs       = def f (args ++ xs)
(lam v t)    $ (x ∷ xs) = (substTop (unArg x) t) $ xs
(pi a b)     $ (x ∷ xs) = error "a pi is not a function"
set          $ (x ∷ xs) = error "set is not a function"
unknown      $ xs       = unknown

data Telescope : Set where
  [] : Telescope
  _∷_ : Term → Telescope → Telescope

instance
  SubstTelescope : Subst Telescope
  SubstTelescope = record { applySubst = substTelescope }
    where
      substTelescope : Substitution → Telescope → Telescope
      substTelescope σ [] = []
      substTelescope σ (ty ∷ tel) = ty [ σ ] ∷ substTelescope (liftS 1 σ) tel

data DefView : Term → Set where
  instance
    defView : ∀ {f xs} → DefView (def f xs)

defName : ∀ t {{_ : DefView t}} → Name
defName ._ {{defView {f} {_}}} = f

data PiView : Term → Set where
  instance
    piView : ∀ {a b} → PiView (pi a b)

piInfo : ∀ t {{_ : PiView t}} → ArgInfo
piInfo ._ {{piView {arg i _} {_}}} = i

piDom : ∀ t {{_ : PiView t}} → Term
piDom ._  {{piView {arg _ a} {_}}} = a

piCod : ∀ t → {{_ : PiView t}} → Term
piCod ._  {{piView {_} {b}}} = b

data SetView : Term → Set where
  instance
    setView : SetView set

record Parse (T : Set) : Set where
  field parse : Builtin.Term → T
open Parse {{...}} public

parseArgs : ∀ {T} {{_ : Parse T}} →
            List (Arg Builtin.Term) → List (Arg T)
parseArgs = map (fmap parse)

instance
  {-# TERMINATING #-}
  ParseTerm  : Parse Term

ParseTerm = record { parse = parseTerm }
  where
    parseTerm : Builtin.Term → Term
    parseTerm (Builtin.var i args) = var i (parseArgs args)
    parseTerm (Builtin.con c args) = con c (parseArgs args)
    parseTerm (Builtin.def f args) = def f (parseArgs args)
    parseTerm (Builtin.lam v (abs _ t)) = lam v (parse t)
    parseTerm (Builtin.pi a (abs _ b)) = pi (fmap (parse ∘ unEl) a) (parse (unEl b))
    parseTerm (Builtin.sort s) = set
    parseTerm (Builtin.lit (Builtin.nat zero)) = con (quote Nat.zero) []
    parseTerm (Builtin.lit (Builtin.nat (suc n))) = con (quote Nat.suc) (vArg (parse (Builtin.lit (Builtin.nat n))) ∷ [])
    parseTerm _ = unknown

record Compile (T : Set) : Set where
  field compile : T → Builtin.Term
open Compile {{...}} public

compileArgs : ∀ {T} {{_ : Compile T}} →
              List (Arg T) → List (Arg Builtin.Term)
compileArgs = map (fmap compile)

instance
  {-# TERMINATING #-}
  CompileTerm : Compile Term

CompileTerm = record { compile = compileTerm }
  where
    compileTerm : Term → Builtin.Term
    compileTerm (var i args) = Builtin.var i (map (fmap compile) args)
    compileTerm (con c args) = Builtin.con c (map (fmap compile) args)
    compileTerm (def f args) = Builtin.def f (map (fmap compile) args)
    compileTerm (lam v t) = Builtin.lam v (abs "" (compile t))
    compileTerm (pi a b) = Builtin.pi (fmap (el Builtin.unknown ∘ compile) a) (abs "" (el Builtin.unknown (compile b)))
    compileTerm set = Builtin.sort Builtin.unknown
    compileTerm unknown = Builtin.unknown

typeOf : Name → Term
typeOf = parse ∘ unEl ∘ Builtin.typeOf

piApply : Term → Args → Term
piApply t []       = t
piApply (pi a b) (x ∷ xs) = piApply (substTop (unArg x) b) xs
piApply _ (x ∷ xs) = error "not enough pie"

instance
  EqSetView : ∀ {t} → Eq (SetView t)
  EqSetView = record{ _==_ = eq }
    where
      eq : ∀ {t} → (v₁ v₂ : SetView t) → Dec (v₁ ≡ v₂)
      unquoteDef eq = deriveEqDef (quote SetView)

instance
  EqPiView : ∀ {t} → Eq (PiView t)
  EqPiView = record{ _==_ = eq }
    where
      eq : ∀ {t} → (v₁ v₂ : PiView t) → Dec (v₁ ≡ v₂)
      unquoteDef eq = deriveEqDef (quote PiView)

instance
  {-# TERMINATING #-}
  EqSubst : Eq Substitution
  EqTerm  : Eq Term

  EqSubst = record{ _==_ = eq }
    where
      eq : (σ₁ σ₂ : Substitution) → Dec (σ₁ ≡ σ₂)
      unquoteDef eq = deriveEqDef (quote Substitution)

  EqTerm = record{ _==_ = eq }
    where
      eq : (t₁ t₂ : Term) → Dec (t₁ ≡ t₂)
      unquoteDef eq = deriveEqDef (quote Term)
