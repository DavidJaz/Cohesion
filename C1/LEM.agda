{-# OPTIONS --without-K #-}

module C1.LEM where
  open import Basics
  open import Bool
  open import LEM
  open import NotNot
  open import Flat
  open import Sharp
  open import C1.Base

  open import lib.NType2
   
    
  -- UNFINISHED due to ♯-ptwise problems
  ♯-prop-is-¬¬ : ∀ {i}(P : Prop i) (p : (P holds) is-codiscrete) → (P holds) ≃ ((not (not P)) holds)
  ♯-prop-is-¬¬ P p =
    iff-to-≃ {P = P} {Q = not (not P)}
      -- ⇒
         continue
      -- ⇐
         (not (not P) holds
           –⟨ lemma ⟩→
         ♯ (P holds)
           –⟨ un♯ p ⟩→
         P holds
           →∎)
    where
      postulate lemma : not (not P) holds → ♯ (P holds)
      -- The problem here is that ♯-ptwise won't rewrite to ♯ (P holds)
      -- So, we can't run the right proof.
      -- I'm not sure why though...

  
  nbhd-is-infinitesimal : ∀ {i} {A : hSet i} (a : ∈ A) → (nbhd a) is-infinitesimal
  nbhd-is-infinitesimal {A = (A , p)} a =
    has-level-in (((a , refl≈)^♯) ,
      (λ b' → ♯-=-retract $
                let♯ b ^♯:= b' in♯
                  (♯-=-compare
                    (<– (♯-prop-is-¬¬ (♯ₙ $ (a , refl≈) ==ₚ b)
                    (♯-is-codiscrete ((a , refl≈) == b)))
                    {!snd b!})) ^♯
                in-family (λ b' → ((a , refl≈)^♯) == b')))
