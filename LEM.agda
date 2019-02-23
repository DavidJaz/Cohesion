{-# OPTIONS --without-K #-}

module LEM where
  open import Basics
  open import Flat
  open import Bool

  open import lib.Basics
  open import lib.types.Bool
  open import Bool
  open import lib.NType2


  open import Axiom.LEM public

  
  flat-set-has-dec-eq : {i :{♭} ULevel} (A :{♭} hSet i)
                        → has-dec-eq (♭ (∈ A))
  flat-set-has-dec-eq A  =
    λ {(x ^♭) (y ^♭) → LEM (_==ₚ_ {A = ♭ₙ A} (x ^♭) (y ^♭))}

  discrete-set-has-dec-eq : {i :{♭} ULevel} (A :{♭} hSet i)
                            → (_ :{♭} (∈ A) is-discrete) → has-dec-eq (∈ A)
  discrete-set-has-dec-eq A p = transport has-dec-eq (discrete-id p) (flat-set-has-dec-eq A)

  _=bool=ₚ_ : {i :{♭} ULevel} {A :{♭} hSet i} {p :{♭} (∈ A) is-discrete} (x y : ∈ A) → Bool
  _=bool=ₚ_ {A = A} {p = p} x y = _=bool=_ {_} {∈ A} {discrete-set-has-dec-eq A p} x y

  
  un¬¬-crisp : {i :{♭} ULevel} {P :{♭} Prop i} (nnp : ¬ (¬ (P holds))) → P holds
  un¬¬-crisp {P = P} nnp with (LEM P)
  ...                    |    (inl p)  = p
  ...                    |    (inr np) = quodlibet (nnp np)
