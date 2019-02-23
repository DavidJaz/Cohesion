{-# OPTIONS --without-K #-}

open import Basics
open import lib.Basics
open import Flat

module Axiom.C0 {i j :{♭} ULevel} (I :{♭} Type i) (R :{♭} I → Type j) where
    postulate C0 : {k :{♭} ULevel} (A :{♭} Type k)
                   (p : (index : I) → (is-equiv (λ (a : A) → λ (r : R index) → a)))
                   → A is-discrete
                 
