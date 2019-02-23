{-# OPTIONS --without-K #-}

open import lib.Basics

module C1 {i₁ j₁ :{♭} ULevel}
          (I :{♭} Type i₁)
          (R :{♭} I → Type j₁)
          (r₀ :{♭} (index : I) → R index) where
  -- We assume the family R satisfies Axiom C0
  open import Axiom.C0 {i₁} {j₁} I R
  

  open import Basics
  open import Flat
  open import Sharp
  open import lib.types.Bool
  open import Bool

  open import lib.Equivalence2
  open import lib.types.Coproduct

  _is-discrete-C0 : {i : ULevel} (A : Type i) → Type _
  _is-discrete-C0 {i} A = (index : I) → (is-equiv {i = i} (λ (a : A) → (λ (r : R index) → a)))

  discrete-C0-eq : {i : ULevel} {A : Type i} (p : A is-discrete-C0) (index : I)
                   → A ≃ ((R index) → A)
  discrete-C0-eq p index = _ , (p index)
                   

  prop-is-discrete-C0 : {i : ULevel} (P : Prop i) → (P holds) is-discrete-C0
  prop-is-discrete-C0 P =
    (λ index →
      is-eq to
            fro
            (λ f → λ= (λ r → prop-path (P holds-is-a-prop) (f (r₀ index)) (f r)))
            (λ p → prop-path (P holds-is-a-prop) (fro {index} (to p)) p))
      where
        to : {index : I} → P holds → (r : R index) → P holds
        to = λ p _ → p

        fro : {index : I} → ((r : R index) → P holds) → P holds
        fro {index} = λ f → f (r₀ index)

  crisp-prop-is-discrete : {i :{♭} ULevel} (P :{♭} Prop i) → (P holds) is-discrete
  crisp-prop-is-discrete P = C0 (P holds) (prop-is-discrete-C0 P)

  ⊥-is-discrete : ⊥ is-discrete
  ⊥-is-discrete = crisp-prop-is-discrete False

  -- Mapping into a C0 discrete gives a C0 discrete space.
  -- The argument is by swapping the order of application.
  Π-♭-C0 : {i j : ULevel} {A : Type i}
           {B : A → Type j} (p : (a : A) → (B a) is-discrete-C0)
           → ((a : A) → B a) is-discrete-C0
  Π-♭-C0 {A = A} {B = B} p =
    λ index → _ is-an-equivalence-because
      (fro index) is-inverse-by
        to-fro index and fro-to index
    where
      fro : (index : I) → ((R index) → (a : A) → B a) → (a : A) → B a
      fro index f a = (<– (discrete-C0-eq (p a) index)) (λ r → f r a)

      abstract
        to-fro : ∀ index f → (λ _ → fro index f) == f
        to-fro index f = -- We swap the order of r and a and use the discreteness of B a
          λ= $ λ r →
            λ= $ λ a →
              app= (lemma a) r
          where
            lemma : ∀ a → (λ _ → fro index f a) == (λ r → f r a)
            lemma a = <–-inv-r (discrete-C0-eq (p a) index) $ λ r → f r a

        fro-to : ∀ index f → (fro index (λ _ → f)) == f
        fro-to index f =
          λ= $ λ a →
            <–-inv-l (discrete-C0-eq (p a) index) $ f a

  -- Crisp propositions are codiscrete
  crisp-prop-is-codiscrete : {i :{♭} ULevel} (P :{♭} Prop i) → (P holds) is-codiscrete
  crisp-prop-is-codiscrete P =
    (P holds) is-codiscrete-because -- We give the map going the other way:
      ♯ (P holds) –⟨ map₁ ⟩→ ♭ (♯ (P holds)) –⟨ map₂ ⟩→ ♭ (P holds) –⟨ _↓♭ ⟩→ P holds →∎
        is-retract-by (λ _ → prop-path (snd P) _ _)
    where
      map₁ : ♯ (P holds) → ♭ (♯ (P holds))
      map₁ = <– (discrete-eq (crisp-prop-is-discrete (♯ₙ P)))
      
      map₂ : ♭ (♯ (P holds)) → ♭ (P holds)
      map₂ = –> ♭♯-eq

  ¬-is-codiscrete : ∀ {i} (A : Type i) → (¬ A) is-codiscrete
  ¬-is-codiscrete {i} A = -- mapping into a codiscrete is codiscrete.
    replete (Π-codisc {A = A} (λ _ → ⊥)) (lemma₁ ⁻¹)
    where
      lemma₁ : (A → ⊥) ≃ (A → ♯ ⊥)-- ⊥ is codiscrete b/c it is crisp.
      lemma₁ = post∘-equiv (codisc-eq (crisp-prop-is-codiscrete False))

      open import lib.types.Modality
      replete = (Modality.local-is-replete {i}) ♯-modality

  ♭-commutes-with-¬ : {i :{♭} ULevel} {A :{♭} Type i} → ♭ (¬ A) ≃ ¬ (♭ A)
  ♭-commutes-with-¬ {i = i} {A = A} =
                    ♭ (¬ A)
                  ≃⟨ ♭→e {A = ¬ A} {B = A → ♯ ⊥} lemma₁ ⟩
                    ♭ (A → ♯ ⊥)
                  ≃⟨ ♭♯-adjoint ⁻¹ ⟩
                     ♭ (¬ (♭ A))
                  ≃⟨ discrete-eq (crisp-prop-is-discrete (¬ (♭ A) , proof)) ⟩
                     ¬ (♭ A)
                  ≃∎
    where
      lemma₁ : (A → ⊥) ≃ (A → ♯ ⊥)-- ⊥ is codiscrete b/c it is crisp.
      lemma₁ = post∘-equiv (codisc-eq (crisp-prop-is-codiscrete False))

      proof : ¬ (♭ A) is-a-prop
      proof = mapping-into-prop-is-a-prop (λ _ → False holds-is-a-prop)

  -- Hereafter, we use LEM
  open import LEM
  open import NotNot

  module _ {i :{♭} ULevel} where
    record Γ : Type (lsucc i) where
      constructor ctx
      field
        ᶜP : Prop i
        ᶜnnp : ¬¬ (ᶜP holds) holds
    open Γ
    
    ♯-prop-is-¬¬ : (P : Prop i) → ((♯ₙ P) holds) ≃ ((¬¬ (P holds)) holds)
    ♯-prop-is-¬¬ P =
      iff-to-≃ {P = ♯ₙ P} {Q = ¬¬ (P holds)}
        -- ⇒
        (♯ₙ P holds
          –⟨ (λ a → let♯ u ^♯:= a in♯ ((continue u) ^♯)) ⟩→
        ♯ₙ (¬¬ (P holds)) holds
          –⟨ un♯ (¬-is-codiscrete (¬ (P holds))) ⟩→
        ¬¬ (P holds) holds
          →∎)
      -- ⇐
        (λ nnp → {!let♯ γ ::= (ctx P nnp) in♯ (helper (ᶜP γ) (ᶜnnp γ)) ^^♯-in-family (λ (γ :{♭} Γ) → (ᶜP γ) holds) !})
      where
        helper : (P :{♭} Prop i) → ((¬¬ (P holds)) holds) ::→ (P holds)
        helper P nnp = (un¬¬-crisp {P = P} nnp)
  
  -- C1 and LEM give us an equivalence between the crisp propositions and the booleans.
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
