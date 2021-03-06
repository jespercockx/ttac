module Ttac where

open import Prelude hiding (id; [_]; _,_)
open import Integer
open import Data.List
open import Builtin.Reflection as Builtin using (Arg; unArg; unEl; vArg)
open import Untyped renaming (Term to UTerm) hiding (compile)
open import UntypedEquality
open import Typed

ttac : (Γ : List (Arg Builtin.Type)) (ty : Builtin.Term) →
        Term (parseCtx Γ) (Untyped.parse ty) →
        Builtin.Term
ttac Γ ty x = compile x

module Tests where

  pattern `Nat = def (quote Nat) []
  pattern `zero = con (quote Nat.zero) []
  pattern `suc n = con (quote Nat.suc) (vArg n ∷ [])
  pattern `Vec A n = def (quote Vec) (vArg A ∷ vArg n ∷ [])

  test-var' : Term (∅ , `Nat , `Vec `Nat (var 0 [])) (`Vec `Nat (var 1 []))
  test-var' = var zero []

  test-var : (n : Nat) → Vec Nat n → Vec Nat n
  test-var n v = unquote (compile test-var')

  test-con' : Term ∅ `Nat
  test-con' = con (quote Nat.suc) (con (quote Nat.zero) [] ∷′ [])

  test-con = unquote (compile test-con')

  test-def' : Term ∅ set
  test-def' = def (quote Vec) (unknown ∷′ def (quote Nat) [] ∷′ con (quote Nat.zero) [] ∷′ [])

  test-def = unquote (compile test-def')

  test-lam' : Term ∅ (pi (vArg `Nat) `Nat)
  test-lam' = lam′ (def (quote Nat) []) (con (quote Nat.suc) (con (quote Nat.suc) (var zero [] ∷′ []) ∷′ []))

  test-lam = unquote (compile test-lam')

  test-pi' : Term ∅ set
  test-pi' = pi (vArg `Nat) (def (quote Vec) (unknown ∷′ def (quote Nat) [] ∷′ var zero [] ∷′ []))

  test-pi = unquote (compile test-pi')

  test-tac : (x y : Nat) → x ≡ y → y ≡ x
  test-tac x y = tactic ttac
    (lam′
      (def (quote _≡_)
        (  def (quote lzero)    []′
        ∷′ def (quote Nat)      []′
        ∷′ var (suc zero)       []′
        ∷′ var zero             []′
        ∷′ []′))
      (def (quote sym)
        (  def (quote lzero)    []′
        ∷′ def (quote Nat)      []′
        ∷′ var (suc (suc zero)) []′
        ∷′ var (suc zero)       []′
        ∷′ var zero []′ ∷′ []′)))
