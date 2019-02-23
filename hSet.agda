{-# OPTIONS --without-K #-}

module hSet where
  
  open import lib.Basics
  open import lib.Funext
  open import lib.NType2
  open import lib.types.Truncation
  open import lib.types.Bool
  open import Prop

  _is-a-set : {i : ULevel} (A : Type i) → Type i
  A is-a-set = is-set A

  -- To get an element a of the set A is to give a : ∈ A.
  ∈ : {i : ULevel} (A : hSet i) → Type i
  ∈ = fst

  set-is-a-set : {i : ULevel} (A : hSet i) → (∈ A) is-a-set
  set-is-a-set A = snd A

  -- Equality for sets, landing in Prop
  _==ₚ_ : {i : ULevel} {A : hSet i}
          → (x y : ∈ A) → Prop i
  _==ₚ_ {_} {A} x y = (x == y) , has-level-apply (set-is-a-set A) x y

  _=bool=_ : {i : ULevel} {A : Type i} {p : has-dec-eq A}
             → (x y : A) → Bool
  _=bool=_ {p = p} x y  = case (p x y)
    where case : Dec (x == y) → Bool
          case (inl _) = true
          case (inr _) = false

  ∥_∥₀ : ∀ {i} (A : Type i) → Type i
  ∥_∥₀ = Trunc 0
