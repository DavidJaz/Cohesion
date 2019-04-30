{-# OPTIONS --without-K #-}

module Conaturals where
  open import Basics
  open import Bool
  open import lib.Basics
  open import lib.types.Nat
  open import lib.types.Bool

  {-

  _is-increasing-b : (ℕ → Bool) → Type _
  P is-increasing-b = (n m : ℕ) → n ≤ m → (P n) holds-b → (P m) holds-b

  increasing-b-is-a-prop : (P : ℕ → Bool) → (P is-increasing-b) is-a-prop
  increasing-b-is-a-prop P =
    mp (λ _ → mp (λ x → mp (λ _ → mp (λ _ → (Bool-to-Prop₀ (P x)) holds-is-a-prop ))))
    where mp = mapping-into-prop-is-a-prop

  ℕ∞-prop : SubtypeProp (ℕ → Bool) _
  ℕ∞-prop = _is-increasing-b , increasing-b-is-a-prop

  ℕ∞ : Type₀
  ℕ∞ = Subtype ℕ∞-prop

  -}
  
  -- I'm having trouble using coinduction =[ 
  -- The type of conatural numbers
  record ℕ∞ : Type₀ where
    coinductive
    field
      pred∞ : ℕ∞ ⊔ ⊤
    pattern go∞ x = inl x
    pattern stop∞ = inr unit
  open ℕ∞ public
  
  coO : ℕ∞
  pred∞ coO = stop∞

  co∞ : ℕ∞
  pred∞ co∞ = go∞ co∞

  suc∞ : ℕ∞ → ℕ∞
  pred∞ (suc∞ x) = go∞ x

  instance
    ℕ-to-ℕ∞ : ℕ → ℕ∞
    ℕ-to-ℕ∞ O = coO
    ℕ-to-ℕ∞ (S n) = suc∞ (ℕ-to-ℕ∞ n)

  case-pred∞_of_ : {i : ULevel} {A : Type i}
                  (n : ℕ∞) (f :  ℕ∞ ⊔ ⊤ → A)
                  → A
  case-pred∞ n of f = f (pred∞ n)
  {- 
    For a paradigmatic use of this function, see below:
  -}


  pred∞-is-coO : ℕ∞ → Bool
  pred∞-is-coO n =
    case-pred∞ n of (λ {
      (go∞ _) → false ;
      stop∞   → true   })

  case∞ : {i : ULevel} {A : Type i}
          (a : A) (f : ℕ∞ → A)
          → ℕ∞ → A
  case∞ a f n = case-pred∞ n of (λ {
                   stop∞ → a       ;
                   (go∞ x) → f x   })

  syntax case∞ a (λ m → t) n = case∞ n of-co0→ a suc∞- m -→ t 

  instance
    ℕ∞-to-ℕ→Prop : ℕ∞ → (ℕ → Bool)
    ℕ∞-to-ℕ→Prop n = case∞ n
                       of-co0→ (λ _ → true )
                       suc∞- m -→ {! λ { O → false ; (S k) → ℕ∞-to-ℕ→Prop m k }!}
    {- ℕ∞-to-ℕ→Prop n O = pred∞-is-coO n
        
    ℕ∞-to-ℕ→Prop n (S k) = {!helperS (pred∞ n) k!}
      where
        helperS : ℕ∞ ⊔ ⊤ → ℕ → Bool
        helperS (go∞ pn) O = {!!}
        helperS (go∞ pn) (S k) = {!!}
        helperS stop∞ k = true -}
