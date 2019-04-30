{-# OPTIONS --without-K #-}

module LogicalTopology where
  open import Basics

  open import lib.types.Truncation

  -- For convenience, we define the "power type" ℘ A
  ℘ : {i : ULevel} (j : ULevel) (A : Type i) → Type _
  ℘ j A = A → Prop j

  _∩_ : {i j k : ULevel} {A : Type i}
        → ℘ j A → ℘ k A → ℘ _ A
  U ∩ V = λ a → (U a) ∧ (V a)

  _∪_ : ∀ {i j k} {A : Type i}
        → ℘ j A → ℘ k A → ℘ _ A
  P ∪ Q = λ a → (P a) ∨ (Q a)

  ⋃ : {i j : ULevel} {A : Type i}
      {I : Type j} (U : I → ℘ (lmax i j) A)
      → ℘ _ A
  ⋃ U = λ a → ∃ₚ λ i → (U i a)

  infix 30 _⊆_
  _⊆_ : ∀ {i j k} {A : Type i} (P : ℘ j A) (Q : ℘ k A)
        → Prop _
  _⊆_ {A = A} P Q = ∀ₚ \(a : A) → (P a) ⇒ (Q a)

  -- The definition of logically (Penon) open.
  _is-open : {i j : ULevel} {A : Type i} (U : ℘ j A) → Type (lmax i j)
  U is-open = ∀ x y → (p : (U x) holds) → ∥ (x ≠ y) ⊔ ((U y) holds) ∥

  _is-closed : ∀ {i j} {A : Type i} (U : ℘ j A) → Type (lmax i j)
  C is-closed = (not ∘ C) is-open

  maps-are-cts : {i j k : ULevel} {A : Type i} {B : Type j}
                 {f : A → B} {U : ℘ k B} (p : U is-open)
                 → (U ∘ f) is-open
  maps-are-cts {A = A} {f = f} {U = U} p x y q =
    let[ p' ]:= (p (f x) (f y) q) in-
      [ (case₀ ⊔→ case₁) p' ]
    where
      case₀ : (f x ≠ f y) → x ≠ y
      case₀ ne p = ne (ap f p)

      case₁ : (U (f y)) holds → (U (f y)) holds
      case₁ z = z

  maps-are-cts-closed : {i j k : ULevel} {A : Type i} {B : Type j}
                        {f : A → B} {C : ℘ k B} (p : C is-closed)
                        → (C ∘ f) is-closed
  maps-are-cts-closed {C = C} = maps-are-cts {U = not ∘ C}

  unions-of-opens-are-open : {i j : ULevel} {A : Type i}
                             {I : Type j} (U : I → ℘ _ A)
                             (o : (i : I) → (U i) is-open)
                             → (⋃ U) is-open
  unions-of-opens-are-open U o x y p = -- Supposing that x is in ⋃ U,
    let[ q ]:= p in- -- We know that x is in some particular U i (i ≡ fst q), so
      let[ z ]:= (o (fst q) x y (snd q)) in- -- we use the open-ness of U i to split into two cases
           [ z |> -- z : (x ≠ y) ⊔ (U i y) holds
             ((idf (x ≠ y)) -- Case₀: x already isn't y
                   ⊔→
             ((λ (w : U (fst q) y holds) → -- Case₁: y is in U i and therefore ⋃ U
               [ (fst q) , w ])))
           ]                   

  
  _is-logically-connected : ∀ {i j} {A : Type i} (U : ℘ j A) → Prop _
  _is-logically-connected {j = j} {A = A} U =
    ∀ₚ λ (P : ℘ j A) → (U ⊆ (P ∪ (not ∘ P)))
                     ⇒ ((U ⊆ P) ∨ (U ⊆ not ∘ P))

  _is-detachable : ∀ {i j} {A : Type i} (P : ℘ j A) → Prop _
  _is-detachable {A = A} P =
    ∀ₚ λ (a : A) → (P a) ∨ (not $ P a)

  _is-inhabited : ∀ {i j} {A : Type i} (P : ℘ j A) → Prop _
  _is-inhabited {A = A} P =
    ∃ₚ λ (a : A) → P a

  _is-logical-ctd-cmp : ∀ {i j} {A : Type i} (P : ℘ j A) → Prop _
  P is-logical-ctd-cmp =
    (P is-inhabited) ∧
    (P is-detachable) ∧
    (P is-logically-connected)
