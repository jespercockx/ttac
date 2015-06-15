{-# OPTIONS --no-positivity-check #-}

open import Prelude hiding (id; _$_; [_])
open import Data.List using (Any; forgetAny) renaming (_∈_ to _l∈_)
open import Builtin.Reflection as Builtin using
  ( Arg; arg; unArg; ArgInfo; arg-info; vArg; hArg
  ; Abs; abs
  ; el; unEl
  ; Visibility; visible; hidden; instance′; visibility
  ; Relevance; relevant
  ; Name
  )
open import Tactic.Reflection.Telescope using (telView)
open import Integer
open import Untyped

module Semantics where

data Dom : Set where
  Con : (c : Name) (args : List (Arg Dom)) → Dom
  Lam : (v : Visibility) → (Dom → Dom) → Dom
  Pi  : (a : Arg Dom) (b : Dom → Dom) → Dom
  Type : Dom
  Unknown : Dom
  Neutral : Term → Dom

_·_ : Dom → Dom → Dom
(Lam _ f) · v = f v
f · v = Unknown

{-# TERMINATING #-}
↑ : Dom → Term → Dom
↓ : Nat → Dom → Dom → Term

↑ (Pi (arg i a) b) t = Lam (visibility i) (λ v → ↑ (b v) (t $ (arg i (↓ 0 a v) ∷ [])))
↑ ty t = Neutral t

↓ k Type (Pi a b) = pi (fmap (↓ k Type) a) (↓ (suc k) Type (b (↑ (unArg a) (var {!!} []))))
↓ k Type Type = set
↓ k (Pi (arg i a) b) v = lam (visibility i) (↓ (suc k) (b {!!}) (v · {!!}))
↓ k ty (Neutral t) = t [ wk k id ]
↓ k ty v = unknown
