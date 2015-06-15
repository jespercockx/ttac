open import Prelude hiding (id; [_])
open import Integer

open import Builtin.Reflection as Builtin using
  ( Arg; arg; unArg; ArgInfo; arg-info; vArg; hArg
  ; Abs; abs
  ; el; unEl
  ; Visibility; visible; hidden; instance′
  ; Relevance; relevant
  ; Name
  ; Function; fun-def; Definition; definitionOf; function
  ) public

open import Untyped
open import Tactic.Deriving.Eq

data Pattern : Set where
  con    : (c : Name) (args : List (Arg Pattern)) → Pattern
  dot    : Pattern
  var    : Pattern
  absurd : Pattern
  unknown : Pattern

{-# TERMINATING #-}
parsePattern : Builtin.Pattern → Pattern
parsePatterns : List (Arg Builtin.Pattern) → List (Arg Pattern)

parsePatterns = map (fmap parsePattern)
parsePattern (Builtin.con c args) = con c (parsePatterns args)
parsePattern Builtin.dot = dot
parsePattern (Builtin.var s) = var
parsePattern (Builtin.lit (Builtin.nat zero)) = con (quote Nat.zero) []
parsePattern (Builtin.lit (Builtin.nat (suc n))) = con (quote Nat.suc) (vArg (parsePattern (Builtin.lit (Builtin.nat n))) ∷ [])
parsePattern Builtin.absurd = absurd
parsePattern _ = unknown

data Clause : Set where
  clause : (pats : List (Arg Pattern)) (rhs : Term) → Clause
  absurd : (pats : List (Arg Pattern)) → Clause

parseClause : Builtin.Clause → Clause
parseClause (Builtin.clause pats rhs) = clause (parsePatterns pats) (parse rhs)
parseClause (Builtin.absurd-clause pats) = absurd (parsePatterns pats)

data Match : Set where
  positive : List Term → Match
  negative : Match
  dontknow : String → Match

data Reduction : Set where
  reduced  : Term → Reduction
  mismatch : Reduction
  dontknow : String → Reduction

instance
  EqReduction : Eq Reduction
  EqReduction = record{ _==_ = eq }
    where
      eq : (r₁ r₂ : Reduction) → Dec (r₁ ≡ r₂)
      unquoteDef eq = deriveEqDef (quote Reduction)

_&M_ : Match → Match → Match
negative     &M _            = negative
_            &M negative     = negative
dontknow msg &M _            = dontknow msg
_            &M dontknow msg = dontknow msg
positive us  &M positive vs  = positive (vs ++ us)

match : Pattern → Term → Match
matchArgs : List (Arg Pattern) → Args → Match
reduce : Name → Args → Reduction

match (con c args) (var _ _) = dontknow "blocked on var"
match (con c args) (con c' args') =
  if isYes (c == c')
  then matchArgs args args'
  else negative
match (con c args) (def f args') =
  case reduce f args' of λ
    { (reduced t)  → match (con c args) t
    ; mismatch     → dontknow "blocked on def"
    ; (dontknow m) → dontknow m
    }
match (con c args) (lam v t) = dontknow "panic: matching against lambda"
match (con c args) (pi a t)  = dontknow "panic: matching against pi"
match (con c args) set       = dontknow "panic: matching against set"
match (con c args) unknown   = dontknow "blocked on unknown"
match dot          t         = positive []
match var          t         = positive (t ∷ [])
match absurd       t         = negative
match unknown      t         = dontknow "unknown pattern"

matchArgs []             []             = positive []
matchArgs []             (_ ∷ _)        = dontknow "panic: different number of args"
matchArgs (_ ∷ _)        []             = dontknow "panic: different number of args"
matchArgs (arg _ p ∷ ps) (arg _ t ∷ ts) = match p t &M matchArgs ps ts

{-# TERMINATING #-}
parSubst : ∀ {T} {{_ : Subst T}}
           (n : Nat) (args : List Term) → T → T
parSubst n us = applySubst (lift n (foldr sub id us))

parSubstTop : ∀ {T} {{_ : Subst T}}
              (args : List Term) → T → T
parSubstTop = parSubst 0

reduce-clause : Clause → Args → Reduction
reduce-clause (clause pats rhs) args =
  case matchArgs pats args of λ
    { (positive xs) → reduced (parSubstTop xs rhs)
    ; negative      → mismatch
    ; (dontknow m)  → dontknow m
    }
reduce-clause (absurd _)        args = mismatch

reduce-clauses : List Clause → Args → Reduction
reduce-clauses []       args = mismatch
reduce-clauses (c ∷ cs) args =
  case reduce-clause c args of λ
    { (reduced t)  → reduced t
    ; mismatch     → reduce-clauses cs args
    ; (dontknow m) → dontknow m
    }

reduce-function : Function → Args → Reduction
reduce-function (fun-def _ cs) args = reduce-clauses (map parseClause cs) args

reduce f args = case definitionOf f of λ
  { (function x) → reduce-function x args
  ; _            → mismatch
  }

record Normalize (T : Set) : Set where
  field normalize : T → T
open Normalize {{...}} public

instance NormalizeArg  : ∀ {T} {{_ : Normalize T}} → Normalize (Arg T)
NormalizeArg = record { normalize = fmap normalize }

instance NormalizeList : ∀ {T} {{_ : Normalize T}} → Normalize (List T)
NormalizeList = record { normalize = map normalize }

instance
  {-# TERMINATING #-}
  NormalizeTerm : Normalize Term

NormalizeTerm = record { normalize = normalizeTerm }
  where
    normalizeTerm : Term → Term
    normalizeTerm (var i args) = var i (normalize args)
    normalizeTerm (con c args) = con c (normalize args)
    normalizeTerm (def f args) =
      case (reduce f args) of λ
        { (reduced t) → normalize t
        ; _           → def f (normalize args)
        }
    normalizeTerm (lam v t) = lam v (normalize t)
    normalizeTerm (pi a t) = pi (normalize a) (normalize t)
    normalizeTerm set = set
    normalizeTerm unknown = unknown

Normal : ∀ {T} {{_ : Normalize T}} → T → Set
Normal t = normalize t ≡ t

{-
module test where

  test : normalize (def (quote _+_) (vArg (parse (quoteTerm (1 ofType Nat))) ∷ vArg (parse (quoteTerm 1)) ∷ []))
          ≡ parse (quoteTerm 2)
  test = refl

-}
