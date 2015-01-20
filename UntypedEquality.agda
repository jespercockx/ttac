open import Prelude hiding (id; [_])
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
open import Reduce
open import Tactic.Deriving.Eq

data EquivTerm : Term → Term → Set
data EquivSubst : Substitution → Substitution → Set
EquivArg : Arg Term → Arg Term → Set
EquivArgs : Args → Args → Set

data EquivTerm where
  cong-var : ∀ {i xs ys} → EquivArgs xs ys → EquivTerm (var i xs) (var i ys)
  cong-con : ∀ {c xs ys} → EquivArgs xs ys → EquivTerm (con c xs) (con c ys)
  cong-def : ∀ {f xs ys} → EquivArgs xs ys → EquivTerm (def f xs) (def f ys)
  cong-lam : ∀ {v x  y } → EquivTerm x  y  → EquivTerm (lam v x)  (lam v y)
  cong-pi  : ∀ {a a' b b'} → EquivArg a a' → EquivTerm b b' → EquivTerm (pi a b) (pi a' b')
  cong-set : EquivTerm set set
  cong-unknown : EquivTerm unknown unknown

  beta₁ : ∀ {f args s t} {{_ : reduce f args ≡ reduced s}} → EquivTerm s t → EquivTerm (def f args) t
  beta₂ : ∀ {f args s t} {{_ : reduce f args ≡ reduced t}} → EquivTerm s t → EquivTerm s (def f args)

--  cong-subst : ∀ {σ τ s t} → EquivSubst σ τ → EquivTerm s t → EquivTerm (s [ σ ]) (t [ τ ])
--  merge-subst : ∀ {σ τ t} → EquivTerm (t [ σ ] [ τ ]) (t [ σ ◂ τ ])
--  split-subst : ∀ {σ τ t} → EquivTerm (t [ σ ◂ τ ]) (t [ σ ] [ τ ])

data EquivSubst where
  cong-id : EquivSubst id id
  cong-wk : ∀ {i σ τ} → EquivSubst σ τ → EquivSubst (wk i σ) (wk i τ)
  cong-sub : ∀ {s t σ τ} → EquivTerm s t → EquivSubst σ τ → EquivSubst (sub s σ) (sub t τ)
  cong-lift : ∀ {i σ τ} → EquivSubst σ τ → EquivSubst (lift i σ) (lift i τ)

EquivArg (arg i x) (arg i' x') = i ≡ i' × EquivTerm x x'

EquivArgs [] [] = ⊤
EquivArgs (x ∷ xs) (y ∷ ys) = EquivArg x y × EquivArgs xs ys
EquivArgs _ _ = ⊥

instance
  cong-var′ : ∀ {i xs ys} {{_ : EquivArgs xs ys}} → EquivTerm (var i xs) (var i ys)
  cong-var′ {{e}} = cong-var e
  cong-con′ : ∀ {c xs ys} {{_ : EquivArgs xs ys}} → EquivTerm (con c xs) (con c ys)
  cong-con′ {{e}} = cong-con e
  cong-def′ : ∀ {f xs ys} {{_ : EquivArgs xs ys}} → EquivTerm (def f xs) (def f ys)
  cong-def′ {{e}} = cong-def e
  cong-lam′ : ∀ {v x  y } {{_ : EquivTerm x  y }} → EquivTerm (lam v x ) (lam v y )
  cong-lam′ {{e}} = cong-lam e
  cong-pi′  : ∀ {a a' b b'} {{_ : EquivArg a a'}} {{_ : EquivTerm b b'}} → EquivTerm (pi a b) (pi a' b')
  cong-pi′ {{ea}} {{eb}} = cong-pi ea eb
  cong-set′ : EquivTerm set set
  cong-set′ = cong-set
  cong-unknown′ : EquivTerm unknown unknown
  cong-unknown′ = cong-unknown

equiv-refl : ∀ {t} → EquivTerm t t
equiv-refl-arg  : ∀ {x} → EquivArg  x x
equiv-refl-args : ∀ {xs} → EquivArgs xs xs

equiv-refl {var i args} = cong-var equiv-refl-args
equiv-refl {con c args} = cong-con equiv-refl-args
equiv-refl {def f args} = cong-def equiv-refl-args
equiv-refl {lam v t} = cong-lam equiv-refl
equiv-refl {pi a t} = cong-pi (equiv-refl-arg {a}) equiv-refl
equiv-refl {set} = cong-set
equiv-refl {unknown} = cong-unknown

equiv-refl-arg {arg i x} with i == i
equiv-refl-arg {arg i x} | yes _  = refl , equiv-refl
equiv-refl-arg {arg i x} | no neq = ⊥-elim (neq refl)

equiv-refl-args {[]} = tt
equiv-refl-args {x ∷ xs} = equiv-refl-arg {x} , equiv-refl-args

instance
  postulate EqEquivTerm : ∀ {s t} → Eq (EquivTerm s t)
  postulate EqEquivSubst : ∀ {σ τ} → Eq (EquivSubst σ τ)
  postulate EqEquivArg : ∀ {x y} → Eq (EquivArg x y)
  postulate EqEquivArgs : ∀ {xs ys} → Eq (EquivArgs xs ys)

