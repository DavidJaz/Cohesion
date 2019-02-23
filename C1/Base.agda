{-# OPTIONS --without-K #-}

open import lib.Basics

module C1.Base
          {i₁ j₁ :{♭} ULevel}
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
