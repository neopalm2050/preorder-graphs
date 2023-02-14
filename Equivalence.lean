universe u


structure UnionFind where
  obs : Nat
  parent : Fin obs → Fin obs
  has_root : ∀ a:(Fin obs), ∃ b:Nat,
    Nat.repeat parent b a = parent (Nat.repeat parent b a)

def find (uf : UnionFind) (n : Fin uf.obs) : Nat :=
  --let root_exists := uf.has_root n;
  let is_n_root := Nat.decEq n (uf.parent n);
  is_n_root.byCases (
    λ is_root =>
    n
  ) (
    λ not_root =>
    --let not_root : ¬Nat.repeat uf.parent 0 n = uf.parent (Nat.repeat uf.parent 0 n) := Fin.ne_of_val_ne not_root;
    --let a : Nat := n.val.re
    find uf (uf.parent n)
  )
