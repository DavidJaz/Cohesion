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


  ♭Prop₀≃Bool : ♭ Prop₀ ≃ Bool
  ♭Prop₀≃Bool = equiv to fro to-fro fro-to
    where
      to : ♭ Prop₀ → Bool
      to (P ^♭) = Dec-Prop-to-Bool P (LEM P)

      fro : Bool → ♭ Prop₀
      fro = Bool-to-♭Prop₀

      to-fro : (b : Bool) → to (fro b) == b
      to-fro true = Dec-Prop-to-Bool-true-id True (LEM True) unit
      to-fro false = Dec-Prop-to-Bool-false-id False (LEM False) quodlibet

      fro-to : (P : ♭ Prop₀) → fro (to P) == P
      fro-to (P ^♭) = case P (LEM P)
        where
          case₀♭ : (P :{♭} Prop₀) → ♭ (P holds) → fro (to (P ^♭)) == (P ^♭)
          case₀♭ P (p ^♭) = fro (to (P ^♭))
                          =⟨ (ap fro (Dec-Prop-to-Bool-true-id P (LEM P) p)) ⟩
                            fro true -- Since P holds, it equals true
                          =⟨ ! (♭-ap _^♭ (P holds-by p implies-=-True)) ⟩
                            P ^♭
                          =∎

          case₁♭ : (P :{♭} Prop₀) → ♭ (¬ (P holds)) → fro (to (P ^♭)) == (P ^♭)
          case₁♭ P (np ^♭) = fro (to (P ^♭))
                           =⟨ (ap fro (Dec-Prop-to-Bool-false-id P (LEM P) np)) ⟩
                             fro false
                           =⟨ ! (♭-ap _^♭ (¬- P holds-by np implies-=-False)) ⟩
                             P ^♭
                           =∎

          case : (P :{♭} Prop₀) → (d :{♭} Dec (P holds)) → fro (to (P ^♭)) == (P ^♭)
          case P (inl p ) = case₀♭ P (p ^♭)
          case P (inr np) = case₁♭ P (np ^♭)

  {-
  -- We prove that this equivalence preserves the relevant logical structure.
  module ♭Prop₀≃Bool-properties where
    preserves-⇒ : {P Q :{♭} Prop₀} (p : (P ⇒ Q) holds)
                  → (((–> ♭Prop₀≃Bool) (P ^♭)) ≤b ((–> ♭Prop₀≃Bool) (Q ^♭))) holds
    preserves-⇒ {P} {Q} p = {!!}

  -- As a corollary, we find that the points of the upper naturals are the conaturals.
  module Points-Of-Upper-Naturals-Are-Conaturals where
    open import UpperNaturals
    open import Conaturals

    

    theorem : ℕ∞ ≃ ♭ ℕ↑
    theorem = {!!}

-}
