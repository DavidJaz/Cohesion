{-# OPTIONS --without-K #-}

module Axiom.LEM where
  open import Basics
  open import Flat
  open import lib.Basics
  
  postulate LEM : {i :{♭} ULevel} (P :{♭} Prop i) → Dec (P holds)
