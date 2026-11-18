-- The Identity type, defined in `Type` instead of `Prop`.
inductive Path {α : Sort u} : α → α → Type where
  | refl (a : α) : Path a a

-- Uniqueness of Identity proofs for `Path`.
def uip : (p q : Path a b) → Path p q
  | Path.refl _, Path.refl _ => Path.refl _


-- Below is an alternative proof that relies solely on the proof irrelevance of Eq,
-- without resorting to K-like pattern matching.
namespace Path

variable {α : Sort u} {a b c : α}

def symm : Path a b → Path b a
  | refl _ => refl _

def trans : Path a b → Path b c → Path a c
  | refl _, refl _ => refl _

instance : Trans (@Path α) (@Path α) (@Path α) where
  trans := Path.trans

def symm_trans : (p : Path a b) → Path (p.symm.trans p) (refl b)
  | refl _ => refl _

def ap {β : Sort v} (f : α → β) : Path a b → Path (f a) (f b)
  | refl _ => refl _

def toEq : Path a b → a = b
  | refl _ => rfl

def ofEq : a = b → Path a b
  | rfl => refl _

def normalize (p : Path a b) : Path a b := ofEq p.toEq

def normalize_const (p q : Path a b) : Path p.normalize q.normalize := refl _

def canonical : (p : Path a b) → Path ((normalize (refl a)).symm.trans p.normalize) p
  | refl _ => symm_trans _

def uip' (p q : Path a b) : Path p q :=
  calc
    Path p ((normalize (refl a)).symm.trans p.normalize) := (canonical p).symm
    Path _ ((normalize (refl a)).symm.trans q.normalize) := ap _ (normalize_const p q)
    Path _ q := canonical q

end Path
