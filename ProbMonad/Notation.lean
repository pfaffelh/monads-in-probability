import Mathlib

open ENNReal

universe u v
variable {α β : Type u}
variable {γ : Type v}

section some_notation

-- `PMF.pure`: Dirac measure

notation "δ" => PMF.pure -- for the Dirac measure

@[simp]
lemma do_delta (a : α) : (do return ← PMF.pure a) = δ a := PMF.bind_pure (δ a)

@[simp]
lemma do_bind_delta (a : α) : (do let X ← PMF.pure a; return X) = δ a := PMF.bind_pure (δ a)

-- map

infixl:100 "ₓ" => PMF.map

-- Now we can write `f ₓ ℙ` for the image PMF of `ℙ` under `f`.
-- This is usually denoted `PMF.map f ℙ` or `f <$> ℙ`.

@[simp]
lemma map_def (ℙ : PMF α) (f : α → β) : PMF.map f ℙ  = f ₓ ℙ := rfl

-- The next two lemmas require that `α` and `β` live in the same universe!
@[simp]
lemma do_map (ℙ : PMF α) (f : α → β) :
  (do let X ← ℙ; return f X) = f ₓ ℙ := rfl

/-
noncomputable def PMF.prod {n : ℕ} (ℙ : Fin n → PMF α) : PMF (Fin n → α) :=(do let X ← sequence (f := PMF) ℙ; return X)


infixl:71 "⊗" => PMF.prod


@[simp]
lemma do_map₂ (ℙ ℙ' : PMF α) (f : α → α → β) :
  (do let X ← ℙ; let Y ← ℙ'; return f X Y) = (fun (x, y) ↦ f x y) ₓ (ℙ ⊗ ℙ') := by
    simp only [PMF.prod, bind_pure_comp]
    refine PMF.ext ?_
    intro x
    refine DFunLike.congr ?_ rfl
    rw [PMF.map]
    refine PMF.ext ?_
    intro y
    refine DFunLike.congr ?_ rfl

-/

@[simp]
lemma map_def' (ℙ : PMF α) (f : α → β) : f ₓ ℙ = f <$> ℙ := rfl

-- bind

infixl:100 "∘" => PMF.bind

-- Now we can write `ℙ ₓ κ` for the image PMF of `ℙ` under a kernel `κ`.
-- This is usually denoted `PMF.bind ℙ κ` or `ℙ >>= κ`.

lemma bind_def (ℙ : PMF α) (κ : α → PMF β) : ℙ ∘ κ = ℙ.bind κ := by rfl

-- Again, this notation requires that `α` and `β` live in the same universe!
lemma bind_def' (ℙ : PMF α) (κ : α → PMF β) : ℙ >>= κ = ℙ.bind κ := by rfl

@[simp]
lemma do_bind (ℙ : PMF α) (κ : α → PMF β) :
  (do let X ← ℙ; κ X) = (ℙ ∘ κ) := rfl

@[simp]
lemma do_bind' (ℙ : PMF α) (κ : α → PMF β) :
  (do let X ← ℙ; let Y ← κ X; return Y) = (ℙ ∘ κ) := bind_congr (fun _ ↦ bind_pure _)

-- seq

--   In a monad, `mf <*> mx` is the same as
-- `do let f ← mf; x ← mx; pure (f x)`.
noncomputable def seq (ℙ : PMF α) (ℙ' : PMF (α → β)) : PMF β := PMF.seq ℙ' ℙ

-- This feels like evaluating the process `X ← ℙ'` at the random time `T ← ℙ`.
lemma do_seq (ℙ : PMF α) (ℙ' : PMF (α → β)) : (do let X ← ℙ'; let T ← ℙ; return X T) = (ℙ' <*> ℙ) := by rfl


-- join

-- I would call `join ℙ` the first moment measure of the random measure `ℙ`.
noncomputable def join (ℙ : PMF (PMF α)) : PMF α := ℙ ∘ id

@[simp]
lemma do_join (ℙ : PMF (PMF α)) : (do let P ← ℙ; let X ← P; return X) = join ℙ := by
  rw [do_bind']
  rfl

-- Let us look at the laws for `LawfulMonad PMF`.

/- instance : LawfulFunctor PMF where
  map_const := rfl
  id_map := bind_pure
  comp_map _ _ _ := (map_comp _ _ _).symm

instance : LawfulMonad PMF := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)
-/

@[simp]
lemma bind_pure_comp (ℙ : PMF α) (f : α → β) : ℙ ∘ (fun y => δ (f y)) = (f ₓ ℙ) := rfl

lemma id_map (ℙ : PMF α) : id ₓ ℙ = ℙ := by
  exact PMF.map_id ℙ

@[simp]
lemma pure_bind (x : α) (κ : α → PMF α) : δ x ∘ κ = κ x := by
  exact PMF.pure_bind x κ

@[simp]
lemma bind_assoc (ℙ : PMF α) (κ κ' : α → PMF α) : (ℙ ∘ κ) ∘ κ' = ℙ ∘ fun a ↦ κ a∘κ' := by
  exact PMF.bind_bind ℙ κ κ'

@[simp]
lemma map_id (ℙ : PMF α) : id ₓ ℙ = ℙ := by
  exact PMF.map_id ℙ

lemma map_map (ℙ : PMF α) (f : α → β) (g : β → γ) : g ₓ (f ₓ ℙ) = (g ∘ f) ₓ ℙ := by
  exact PMF.map_comp f ℙ g

@[simp]
lemma bind_const (ℙ : PMF α) (ℙ' : PMF β) : ℙ ∘ (Function.const _ ℙ') = ℙ' := by
  exact PMF.bind_const ℙ ℙ'


-- (p : PMF α) (f : α → PMF β) (g : β → PMF γ) :
--   (p.bind f).bind g = p.bind fun a ↦ (f a).bind g
@[simp]
lemma bind_bind (ℙ : PMF α) (κ κ' : α → PMF α) :
    (do let X ← ℙ; let Y ← (κ X); let Z ← κ' Y; return Z) = (do let X ← ℙ; let Z ← ((κ X) ∘ κ'); return Z) := by
  simp only [bind_pure]
  rfl

lemma do_bind_bind (ℙ : PMF α) (κ κ' : α → PMF α) : (do let X ← ℙ; let Y ← (κ X); let Z ← κ' Y; return Z) = ℙ ∘ (fun a ↦ κ a ∘ κ') := by
  rw [bind_bind, do_bind']

lemma do_bind_bind' (ℙ : PMF α) (κ κ' : α → PMF α) : (do let Y ← (do let X ← ℙ; let Y ← (κ X); return Y); let Z ← κ' Y; return Z) = (ℙ ∘ κ) ∘ κ' := by
  rw [do_bind', do_bind']

lemma bind_bind' (ℙ : PMF α) (κ κ' : α → PMF α) :
    (do let Y ← (do let X ← ℙ; let Y ← (κ X); return Y); let Z ← κ' Y; return Z) = (do let X ← ℙ; let Z ← ((κ X) ∘ κ'); return Z) := by
  rw [do_bind', do_bind', do_bind', PMF.bind_bind]

lemma bind_bind'' (ℙ : PMF α) (κ κ' : α → PMF α) :
    (do let Y ← (do let X ← ℙ; let Y ← (κ X); return Y); let Z ← κ' Y; return Z) = (do let X ← ℙ; let Y ← (κ X); let Z ← κ' Y; return Z) := by
  simp only [bind_pure, bind_assoc]
  exact LawfulMonad.bind_assoc ℙ (fun X ↦ κ X) fun Y ↦ κ' Y
