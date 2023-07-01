import UniqueList

universe u

namespace Nat
  theorem repeat_assoc {α : Type u} :
    (f : α → α) →
    (n : Nat) →
    (a : α) →
    Nat.repeat f n (f a) = f (Nat.repeat f n a)
  | f, 0, a => Eq.refl _
  | f, n+1, a => by
    let h : Nat.repeat f (n + 1) (f a) = Nat.repeat f n (f (f a)) := Eq.refl _
    let h' : Nat.repeat f (n + 1) a = Nat.repeat f n (f a) := Eq.refl _
    rw [h, h']
    rw [repeat_assoc f n (f a)]
  
  theorem repeat_add {α : Type u} :
    (f : α → α) →
    (m n : Nat) →
    (a : α) →
    Nat.repeat f m (Nat.repeat f n a) = Nat.repeat f (m + n) a
  | f, m, 0, a => by rfl
  | f, m, n+1, a => repeat_add f m n (f a)
end Nat

def FinArray (size : Nat) :=
  {xs : Array (Fin size) // xs.size = size}

namespace FinArray
  def get {size : Nat} (array : FinArray size) (id : Fin size) : Fin size :=
    array.val.get (
      let in_range : id.val < Array.size array.val := by
        rw [array.property]
        exact id.isLt
      ⟨id.val, in_range⟩
    )
  
  def set {size : Nat} (array : FinArray size) (loc : Fin size) (new : Fin size) : FinArray size :=
    ⟨
      array.val.set (
        let in_range : loc.val < Array.size array.val := by
          rw [array.property]
          exact loc.isLt
        ⟨loc.val, in_range⟩
      ) new,
      (array.val.size_set _ _).trans array.property
    ⟩

  theorem get_set {size : Nat} :
    ∀ array : FinArray size,
    ∀ loc val : Fin size,
    (array.set loc val).get loc = val
  | ⟨⟨list⟩, len_proof⟩, ⟨loc, loc_lt_size⟩, val =>
    let list_len_proof : list.length = size := len_proof
    let list_loc : Fin (list.length) := ⟨loc, by
      rw [list_len_proof]
      exact loc_lt_size
    ⟩
    list.get_set list_loc val

  theorem get_set_ne {size : Nat} :
    ∀ array : FinArray size,
    ∀ setloc getloc val : Fin size,
    setloc ≠ getloc →
    array.get getloc = (array.set setloc val).get getloc
  | ⟨⟨list⟩, len_proof⟩, ⟨setloc, hsetloc⟩, ⟨getloc, hgetloc⟩, val, setloc_ne_getloc =>
    let list_len_proof : list.length = size := len_proof
    let list_setloc : Fin (list.length) := ⟨setloc, by
      rw [list_len_proof]
      exact hsetloc
    ⟩
    let list_getloc : Fin (list.length) := ⟨getloc, by
      rw [list_len_proof]
      exact hgetloc
    ⟩
    let list_setloc_ne_list_getloc : list_setloc ≠ list_getloc := (
      λ equal =>
      let h : setloc = getloc := Fin.val_eq_of_eq equal
      setloc_ne_getloc (Fin.eq_of_val_eq h)
    )
    list.get_set_ne list_setloc list_getloc val list_setloc_ne_list_getloc
end FinArray

def UnionFindLinks (size : Nat) :=
  {
    parent_array : FinArray size //
    ∀ id, ∃ steps,
      let is_root := λ x => parent_array.get x = x
      is_root (Nat.repeat parent_array.get steps id) ∧
      ∀ n, n < steps → ¬(is_root (Nat.repeat parent_array.get n id))
  }


namespace UnionFindLinks

  def parent {size : Nat} (uf : UnionFindLinks size) (id : Fin size) : Fin size :=
    uf.val.get id

  def is_root {size : Nat} (uf : UnionFindLinks size) (id : Fin size) : Prop :=
    uf.parent id = id
  
  def rooted_in_steps {size : Nat} (uf : UnionFindLinks size) (id : Fin size) (steps : Nat) : Prop :=
    uf.is_root (Nat.repeat uf.parent steps id)

  def rooted_in_exact_steps {size : Nat} (uf : UnionFindLinks size) (id : Fin size) (steps : Nat) : Prop :=
    uf.is_root (Nat.repeat uf.parent steps id) ∧
    ∀ n : Nat, n < steps → ¬(uf.is_root (Nat.repeat uf.parent n id))

  def roots {size : Nat} (uf : UnionFindLinks size) : Type :=
    {id : Fin size // uf.is_root id}

  def is_descendency {size : Nat} (uf : UnionFindLinks size) : Fin size → List (Fin size) → Prop
  | _x, [] => True
  | final, (x::xs) => (
    uf.parent x = final ∧ uf.is_descendency x xs
  )

  theorem root_ancestor_root {size : Nat} (uf : UnionFindLinks size) :
    ∀ id steps, uf.is_root id → uf.is_root (Nat.repeat uf.parent steps id) := by
    intro id steps
    induction steps
    case zero =>
      intro h; exact h
    case succ steps h_ind =>
      intro id_is_root
      let hroot := h_ind id_is_root
      let h_eq : uf.parent (Nat.repeat (uf.parent) steps id) = (Nat.repeat (uf.parent) steps id) := hroot
      let associate_parent := Nat.repeat_assoc uf.parent steps id
      rw [associate_parent.symm] at h_eq
      let h_eq : Nat.repeat (parent uf) (steps+1) id = Nat.repeat (parent uf) steps id := h_eq
      rw [h_eq]
      exact hroot

  theorem exact_rooted {size : Nat} (uf : UnionFindLinks size) :
    ∀ id, ∃ steps, uf.rooted_in_exact_steps id steps :=
      uf.property
  
  def from_exact_rooted {size : Nat} :
    (parent_array : FinArray size) →
    (∀ id, ∃ steps,
      let is_root := λ x => parent_array.get x = x
      is_root (Nat.repeat parent_array.get steps id) ∧
      ∀ n, n < steps → ¬(is_root (Nat.repeat parent_array.get n id))
    ) →
    UnionFindLinks size :=
    λ parent_array is_exact_rooted => ⟨parent_array, is_exact_rooted⟩

  theorem rooted {size : Nat} (uf : UnionFindLinks size) :
    ∀ id, ∃ steps, uf.rooted_in_steps id steps :=
      λ id => 
      (uf.exact_rooted id).elim (
        λ steps ⟨rooted_in_steps, _⟩ =>
        ⟨steps, rooted_in_steps⟩
      )
    
  def from_rooted {size : Nat} :
    (parent_array : FinArray size) →
    (∀ id, ∃ steps,
      let r := Nat.repeat parent_array.get steps id
      parent_array.get r = r) →
    UnionFindLinks size
  | parent_array, rooted => ⟨parent_array,
      λ id =>
      (rooted id).elim (by
        intro steps
        induction steps
        case zero =>
          intro h_is_root
          exact ⟨0, h_is_root, 
            λ n n_lt_zero =>
            False.elim (Nat.not_lt_zero n n_lt_zero)
          ⟩
        case succ steps h_ind =>
          intro root_in_succ_steps
          exact (
            let l := Nat.repeat parent_array.get steps id
            if h_steps_root : parent_array.get l = l then
              h_ind h_steps_root
            else
              let is_root := λ x => parent_array.get x = x
              let no_roots_below_aux : ∀ (k : Nat), k < steps + 1 → ¬is_root (Nat.repeat parent_array.get (steps - k) id) := by
                intro k
                induction k
                case zero =>
                  intro _
                  exact h_steps_root
                case succ k h_ind =>
                  intro succ_k_lt_succ_steps
                  let k_lt_steps := Nat.lt_of_succ_lt_succ succ_k_lt_succ_steps
                  let steps_sub_k_ne_zero := Nat.sub_ne_zero_of_lt k_lt_steps
                  let h : steps - (k + 1) = steps - k - 1 := Nat.sub_succ steps k
                  let h' : steps - k - 1 + 1 = steps - k := Nat.succ_pred steps_sub_k_ne_zero
                  intro root_in_succ_n_steps
                  rw [h] at root_in_succ_n_steps
                  rw [h'.symm] at h_ind
                  let k_lt_succ_steps := Nat.lt_of_succ_lt succ_k_lt_succ_steps
                  let ind_h : ¬is_root ( (Nat.repeat parent_array.get (steps - k - 1) (parent_array.get id)) ) := h_ind k_lt_succ_steps
                  let h'' :
                    Nat.repeat parent_array.get (steps - k - 1) (parent_array.get id) =
                    parent_array.get (Nat.repeat parent_array.get (steps - k - 1) id) :=
                    Nat.repeat_assoc parent_array.get (steps - k - 1) id
                  rw [h''] at ind_h
                  rw [root_in_succ_n_steps] at ind_h
                  exact ind_h root_in_succ_n_steps
              
              let no_roots_below : ∀ (n : Nat), n < steps + 1 → ¬is_root (Nat.repeat parent_array.get n id) := by
                intro n n_lt_succ_steps
                let k := steps - n
                let k_le_steps : k ≤ steps := Nat.sub_le steps n
                let n_le_steps : n ≤ steps := Nat.le_of_lt_succ n_lt_succ_steps
                let k_lt_succ_steps : k < steps + 1 := Nat.lt_succ_of_le k_le_steps
                let aux_output := no_roots_below_aux k k_lt_succ_steps
                let steps_eq_n_add_k : steps = n + k := (Nat.eq_add_of_sub_eq n_le_steps (Eq.refl _)).trans (Nat.add_comm k n)
                let steps_sub_k_eq_n : steps - k = n := Nat.sub_eq_of_eq_add steps_eq_n_add_k
                rw [steps_sub_k_eq_n] at aux_output
                exact aux_output

              ⟨steps+1, root_in_succ_steps, no_roots_below⟩
          )
      )
    ⟩
  
  theorem no_cycles {size : Nat} (uf : UnionFindLinks size) :
    ∀ id steps,
      Nat.repeat uf.parent (steps+1) id = id →
      uf.is_root id :=
    λ id steps repeat_in_succ_steps =>
    if hroot : uf.parent id = id then
      hroot
    else
      let cycles_in_succ_steps : ∀ n : Nat, Nat.repeat uf.parent ((steps+1) * n) id = id := by
        intro n
        induction n
        case zero =>
          rfl
        case succ n h_ind =>
          let h : (steps+1) * (n+1) = (steps+1) * n + (steps+1) := by rfl
          rw [h]
          rw [(Nat.repeat_add uf.parent ((steps+1) * n) (steps+1) id).symm]
          rw [repeat_in_succ_steps]
          rw [h_ind]
      
      let multiple_not_root : ∀ n : Nat, ¬uf.is_root (Nat.repeat uf.parent ((steps+1) * n) id) := by
        intro n
        rw [cycles_in_succ_steps n]
        exact hroot
      
      let never_reaching_root : ∀ n : Nat, ¬uf.is_root (Nat.repeat uf.parent n id) :=
        λ n n_is_root =>
        let rem := n % (steps+1)
        let to_next := (steps+1) - rem
        let quot := n / (steps+1)
        let n_sum : (steps+1) * quot + rem = n := Nat.div_add_mod n (steps+1)
        let total_sum : n + to_next = (steps+1) * (quot+1) := by
          rw [n_sum.symm]
          rw [Nat.add_assoc, Nat.add_comm rem to_next]
          let h : to_next = steps + 1 - rem := by rfl
          rw [h]
          let rem_not_large : rem ≤ steps+1 :=
            Nat.le_of_lt (Nat.mod_lt n (Nat.zero_lt_succ steps))
          rw [Nat.sub_add_cancel rem_not_large]
          rfl
        let multiple_is_root := uf.root_ancestor_root (Nat.repeat (parent uf) n id) to_next n_is_root
        (by
          rw [Nat.repeat_add uf.parent to_next n, Nat.add_comm, total_sum] at multiple_is_root
          exact multiple_not_root (quot+1) multiple_is_root
        )
      
      (uf.rooted id).elim (
        λ n rooted_in_n =>
        False.elim (
          never_reaching_root n rooted_in_n
        )
      )

  /-
  def from_no_cycles {size : Nat} :
    (parent_array : FinArray size) →
    (∀ id steps,
      Nat.repeat parent_array.get (steps+1) id = id →
      parent_array.get id = id) →
    UnionFindLinks size
  | parent_array, no_cycles => ⟨parent_array, sorry⟩
  -/

  theorem path_containing_ancestor_end_ends_repeat {size : Nat} (uf : UnionFindLinks size) :
    ∀ id final path, uf.is_descendency final path → path.prop_contains id →
    (∃ steps, Nat.repeat uf.parent steps final = id) →
    ∃ steps, Nat.repeat uf.parent (steps+1) id = id
    | _, _, [] => by intro _ _ _; contradiction
    | id, final, (x::xs) => by
      intro is_desc id_in_xs final_desc_id
      cases id_in_xs
      case inl x_eq_id =>
        exact final_desc_id.elim ( by
          intro n final_to_id_in_n_steps
          rw [is_desc.left.symm, x_eq_id] at final_to_id_in_n_steps
          exact ⟨n, final_to_id_in_n_steps⟩
        )
      case inr id_in_xs =>
        let h := uf.path_containing_ancestor_end_ends_repeat id x xs is_desc.right id_in_xs
        exact final_desc_id.elim ( by
          intro n final_to_id_in_n_steps
          rw [is_desc.left.symm] at final_to_id_in_n_steps
          exact h ⟨n+1, final_to_id_in_n_steps⟩
        )

  theorem path_containing_end_ends_root {size : Nat} (uf : UnionFindLinks size) :
    ∀ id path, uf.is_descendency id path →
    path.prop_contains id → uf.is_root id := 
      λ id path is_desc id_in_path =>
      let id_is_repeat := uf.path_containing_ancestor_end_ends_repeat id id path is_desc id_in_path ⟨0, Eq.refl _⟩
      id_is_repeat.elim (uf.no_cycles id)
  
  theorem non_repeating_path {size : Nat} (uf : UnionFindLinks size) :
    ∀ id path, uf.is_descendency id path → ¬uf.is_root id → (id::path).unique := by
      intro id path is_desc not_root
      constructor
      case left =>
        intro id_in_path
        apply not_root
        let id_is_repeat := uf.path_containing_ancestor_end_ends_repeat id id path is_desc id_in_path ⟨0, Eq.refl _⟩
        exact id_is_repeat.elim (uf.no_cycles id)
      case right =>
        cases path
        case nil =>
          trivial
        case cons x xs =>
          let x_not_root : ¬uf.is_root x := by
            intro x_is_root
            rw [is_desc.left.symm] at not_root
            rw [x_is_root] at not_root
            exact not_root x_is_root
          exact uf.non_repeating_path x xs is_desc.right x_not_root

  def root_distance_aux {size : Nat} (uf : UnionFindLinks size) :
    (id : Fin size) → (n : Nat) →
    (∃ desc : List (Fin size),
      uf.is_descendency id desc ∧
      desc.length + n = size
    ) →
    {
      path_length : Nat //
      uf.rooted_in_exact_steps id path_length
    } :=
    λ id n desc_ex =>
    if hroot : uf.parent id = id then
      ⟨0, hroot, 
        λ _ h _ =>
        Nat.not_lt_zero _ h
      ⟩
    else 
      let parent := uf.parent id
      let next_n := n-1

      let n_ne_zero : n ≠ 0 := desc_ex.elim (
        λ desc ⟨h_desc, h_length⟩ =>

        let next_desc := id :: desc
        
        λ n_eq_zero =>
        let desc_length_size : desc.length = size := by rw [n_eq_zero] at h_length; exact h_length
        let next_desc_larger : next_desc.length = size + 1 := congrArg Nat.succ desc_length_size
        let next_desc_too_big : next_desc.length > size := by
          rw [next_desc_larger]
          exact Nat.lt_succ_self size
        let next_desc_unique : next_desc.unique := uf.non_repeating_path id desc h_desc hroot
        pigeonhole_principle next_desc_unique next_desc_too_big
      )
      
      let next_desc_ex :
        ∃ desc : List (Fin size),
          uf.is_descendency parent desc ∧
          desc.length + next_n = size := desc_ex.elim (
        λ desc ⟨h_desc, h_length⟩ =>
        
        let next_desc := id :: desc
        let next_is_desc : uf.is_descendency parent next_desc :=
          ⟨by rfl, h_desc⟩
        let next_right_length : next_desc.length + next_n = size := by
          rw [(Nat.succ_pred n_ne_zero).symm] at h_length
          let h_length : desc.length + (next_n + 1) = size := h_length
          rw [Nat.add_comm next_n 1, (Nat.add_assoc _ _ _).symm] at h_length
          exact h_length 
        
        ⟨next_desc, next_is_desc, next_right_length⟩
      )

      --not needed apparently? I guess the n_ne_zero already does it?
      --let term : next_n < n := Nat.pred_lt n_ne_zero

      let ⟨parent_root_dist, root_in_dist_steps, not_less_steps⟩ := uf.root_distance_aux parent next_n next_desc_ex
      let our_root_dist := parent_root_dist + 1
      let our_root_dist_proof : uf.is_root (Nat.repeat uf.parent our_root_dist id) := root_in_dist_steps
      let our_first_dist_proof : ∀ (n : Nat),
        n < our_root_dist →
        ¬uf.is_root (Nat.repeat uf.parent n id) := by
        intro n hn
        cases n
        case zero =>
          exact hroot
        case succ n =>
          let hn := Nat.lt_of_succ_lt_succ hn
          exact not_less_steps n hn
      ⟨our_root_dist, our_root_dist_proof, our_first_dist_proof⟩
    

  def root_distance {size : Nat} (uf : UnionFindLinks size) (id : Fin size) : Nat :=
    (uf.root_distance_aux id size ⟨[], trivial, (by rw [Nat.add_comm]; rfl)⟩).val
  
  theorem root_distance_property {size : Nat} (uf : UnionFindLinks size) (id : Fin size) : uf.rooted_in_exact_steps id (uf.root_distance id) :=
    (uf.root_distance_aux id size ⟨[], trivial, (by rw [Nat.add_comm]; rfl)⟩).property

  theorem parent_nearer_root {size : Nat} (uf : UnionFindLinks size) :
    (id : Fin size) →
    (¬uf.is_root id) →
    uf.root_distance (uf.parent id) < uf.root_distance id :=
    λ id not_root =>
    if h : uf.root_distance (uf.parent id) < uf.root_distance id then
      h
    else False.elim (
      let root_distance_not_zero : uf.root_distance id ≠ 0 := by
        intro is_zero
        apply not_root
        let h := (uf.root_distance_property id).left
        rw [is_zero] at h
        exact h
      let h : uf.root_distance id ≤ uf.root_distance (uf.parent id)     := Nat.ge_of_not_lt h
      let h : uf.root_distance id < uf.root_distance (uf.parent id) + 1 := Nat.lt_succ_of_le h
      let h : uf.root_distance id - 1 < uf.root_distance (uf.parent id) := Nat.lt_of_succ_lt_succ (by
        let h' : Nat.succ (uf.root_distance id - 1) = uf.root_distance id := Nat.succ_pred root_distance_not_zero
        rw [h']
        exact h
      )

      (uf.root_distance_property (uf.parent id)).right (uf.root_distance id - 1) h (by
        let h := (uf.root_distance_property id).left
        rw [(Nat.succ_pred root_distance_not_zero).symm] at h
        exact h
      )
    )
  
  def set_to_root_raw {size : Nat} (uf : UnionFindLinks size) :
    Fin size → uf.roots → FinArray size :=
    λ set_loc new_root =>
    uf.val.set set_loc new_root.val
  
  def set_to_root_gives_rooted {size : Nat} (uf : UnionFindLinks size)
    (set_loc : Fin size) (new_root : uf.roots) (id : Fin size) :
    let new_FinArray := uf.set_to_root_raw set_loc new_root
    ∃ steps,
      let r := Nat.repeat new_FinArray.get steps id
      new_FinArray.get r = r :=
    
    let new_FinArray := uf.set_to_root_raw set_loc new_root
    if hchanged : id = set_loc then
      let get_eq_new_root : new_FinArray.get set_loc = new_root.val := uf.val.get_set set_loc new_root.val
      let get_eq_new_root' : new_FinArray.get id = new_root.val := by
        rw [hchanged.symm] at get_eq_new_root
        exact get_eq_new_root
      let get_is_a_root : new_FinArray.get (new_FinArray.get id) = new_FinArray.get id := by
        rw [get_eq_new_root']
        exact if h : set_loc = new_root.val then by
          rw [h] at get_eq_new_root
          exact get_eq_new_root
        else by
          let h' : uf.val.get new_root.val = new_FinArray.get new_root.val := uf.val.get_set_ne set_loc new_root.val new_root.val h
          rw [h'.symm]
          exact new_root.property
      ⟨1, get_is_a_root⟩
    else
      let same_get : uf.parent id = new_FinArray.get id := uf.val.get_set_ne set_loc id new_root.val (λ x => hchanged x.symm)
      if hroot : uf.parent id = id then
        ⟨0, by rw [same_get] at hroot; exact hroot⟩
      else
        --required for termination
        let _hterm : uf.root_distance (uf.parent id) < uf.root_distance id :=
          uf.parent_nearer_root id hroot

        (uf.set_to_root_gives_rooted set_loc new_root (uf.parent id)).elim (
          λ steps hsteps =>
          ⟨steps+1, by rw [same_get] at hsteps; exact hsteps⟩
        )
  termination_by set_to_root_gives_rooted uf set_loc new_root id => uf.root_distance id

  def set_to_root {size : Nat} (uf : UnionFindLinks size) :
    Fin size → uf.roots → UnionFindLinks size :=
    λ set_loc new_root =>
    let new_FinArray := uf.set_to_root_raw set_loc new_root
    let is_rooted := uf.set_to_root_gives_rooted set_loc new_root
    UnionFindLinks.from_rooted new_FinArray is_rooted
  

  def find_aux {size : Nat} (uf : UnionFindLinks size) (id : Fin size) :
    Σ (new_uf : UnionFindLinks size),
      {_root : new_uf.roots //
      (∀ a, uf.is_root a ↔ new_uf.is_root a)} :=
    if hroot : uf.parent id = id then (
      let uf_equiv_uf : ∀ (a : Fin size), uf.is_root a ↔ uf.is_root a :=
        λ a => ⟨λ b => b, λ b => b⟩
      ⟨uf, ⟨id, hroot⟩, uf_equiv_uf⟩
    ) else
      --termination chacking
      let _hterm : uf.root_distance (uf.parent id) < uf.root_distance id :=
        uf.parent_nearer_root id hroot

      let ⟨new_uf, root, old_equiv_new⟩ := uf.find_aux (uf.parent id)
      
      let out_uf : UnionFindLinks size :=
        new_uf.set_to_root id root

      let new_equiv_out : ∀ a, new_uf.is_root a ↔ out_uf.is_root a := by
        intro a
        constructor
        case mp =>
          intro a_is_new_root
          let id_ne_a : id ≠ a := by
            intro id_eq_a
            rw [id_eq_a] at hroot
            exact hroot ((old_equiv_new a).mpr a_is_new_root)
          let parent_unchanged : new_uf.parent a = out_uf.parent a := new_uf.val.get_set_ne id a root.val id_ne_a
          exact parent_unchanged.symm.trans a_is_new_root
        case mpr =>
          intro a_is_out_root
          by_cases id = a
          case inl id_eq_a =>
            let id_is_out_root : out_uf.parent id = id := by
              rw [id_eq_a]
              exact a_is_out_root
            let parent_is_root : out_uf.parent id = root.val := new_uf.val.get_set id root.val
            let id_eq_root : id = root.val := id_is_out_root.symm.trans parent_is_root
            rw [id_eq_root] at hroot
            let root_is_old_root : uf.is_root root.val := (old_equiv_new root.val).mpr root.property
            let _ := hroot root_is_old_root
            contradiction
          case inr id_ne_a =>
            let parent_unchanged : new_uf.parent a = out_uf.parent a := new_uf.val.get_set_ne id a root.val id_ne_a
            exact parent_unchanged.trans a_is_out_root
      
      let root : out_uf.roots := ⟨root.val, (new_equiv_out root.val).mp root.property⟩

      let old_equiv_out : ∀ a, uf.is_root a ↔ out_uf.is_root a :=
        λ a => (old_equiv_new a).trans (new_equiv_out a)

      ⟨out_uf, root, old_equiv_out⟩
  termination_by find_aux uf id => uf.root_distance id

  def find {size:Nat} : Fin size → StateM (UnionFindLinks size) (Fin size)
  | id, uf => (
    let ⟨new_uf, root, _⟩ := uf.find_aux id
    ⟨root.val, new_uf⟩
  )
end UnionFindLinks


--while ranks should store the number of children for each root,
--this isn't really an important invariant or anything, and is only
--there to help the program run faster, so no stored proof
--required for lean to accept.
structure UnionFind (size : Nat) : Type where
  (links : UnionFindLinks size)
  (ranks : {xs : Array Nat // xs.size = size})

namespace UnionFind
  def union {size : Nat} : Fin size → Fin size → StateM (UnionFind size) (Fin size) :=
    λ id1 id2 uf =>
    let uf_links := uf.links
    let ⟨uf_links, root1, _    ⟩ := uf_links.find_aux id1
    let ⟨uf_links, root2, equiv⟩ := uf_links.find_aux id2

    let root1 : uf_links.roots := ⟨root1.val, (equiv root1.val).mp root1.property⟩

    let rank1 := uf.ranks.val.get ⟨
      root1.val,
      by rw [uf.ranks.property]; exact root1.val.isLt
    ⟩

    let rank2 := uf.ranks.val.get ⟨
      root2.val,
      by rw [uf.ranks.property]; exact root2.val.isLt
    ⟩

    let ⟨bigroot, smallroot⟩ :=
      if rank1 < rank2 then
        (root2, root1)
      else
        (root1, root2)
    
    let uf_links := uf_links.set_to_root smallroot.val bigroot
    
    let bigroot_array_loc : Fin uf.ranks.val.size := ⟨
      bigroot.val.val,
      by rw [uf.ranks.property]; exact bigroot.val.isLt
    ⟩

    let new_ranks := uf.ranks.val.set bigroot_array_loc (rank1 + rank2)
    let same_size := uf.ranks.val.size_set bigroot_array_loc (rank1 + rank2)
    let expected_size : new_ranks.size = size := same_size.trans uf.ranks.property

    ⟨bigroot.val, uf_links, new_ranks, expected_size⟩
  
  def find {size : Nat} : Fin size → StateM (UnionFind size) (Fin size) :=
    λ id uf =>
    let ⟨root, uf_links⟩ := do {
      UnionFindLinks.find id
    }.run uf.links
    ⟨root, uf_links, uf.ranks⟩
end UnionFind
