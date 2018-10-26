Module ConcState.
(*Variable conc_state : Type.*)

Inductive conc_state : Type :=
|concstate
|NextState (x: conc_state).

Inductive conc_state_set : Type :=
|Empty 
|Cons (x : conc_state) (s: conc_state_set).



(*Definition conc_state_set := conc_state -> Prop.*)

Fixpoint In (A:conc_state_set) (x:conc_state) : Prop := 
match A with 
|Empty => False
|Cons y s => (y=x) \/ In s x
end.

(*Definition Included (B C:conc_state_set) : Prop := forall x:conc_state, In B x -> In C x.

Inductive Empty_set : conc_state_set :=.*)


(* conc_ex(A) returns ConcState that results from 
the concrete execution of ConcState A  *)

(*Fixpoint in_input_list (l : input_list) (i : input) : Prop :=
match l with
|EmptyList => False
|ConsList item i_list => (item = i) \/ (in_input_list i_list i)
end . *)


(*Fixpoint conc_ex_input_list (states : Ensemble conc_state) (ilist : input_list) : Ensemble conc_state:=
match ilist with
|EmptyList => states
|ConsList inp list_last_elem => conc_ex_input_list (conc_ex states inp) list_last_elem
end.*)


(*Definition singleton (l : conc_state) : Ensemble conc_state :=
  Add conc_state (Empty_set conc_state) l.*)







End ConcState.

Import ConcState.







Module System.
(* System initializes with a defined set of
 initial configuration states, InitStates *)
(*Inductive init_conc_states : Set :=
| IsConc (a : ConcState.conc_state).*)


Definition conc_ex (A: ConcState.conc_state) : ConcState.conc_state := 
match A with
|concstate => NextState A
|NextState x => NextState (NextState x)
end.

Fixpoint conc_ex_n (x: ConcState.conc_state) (n:nat) : ConcState.conc_state :=
match n with
|0 => x
|S n' => conc_ex (conc_ex_n x (n'))
end.

End System.

Import System. 

Module SymbolicExec.

Variable Phi PC : Type.




(*Variable general_set : conc_state_set.*)

(*Definition unif (x : SymbolicExec.sym_state) : conc_state_set := general_set.*)

(* sym_ex(A) returns an object
 in the equivalence class of SymbolicExec
 that results from 
the symbolic execution of an object
in the equivalence class of SymbolicExec A  *)


(*Inductive sym_state : Type :=
|ConstructState (a : Phi) (p : PC)
|SymEx (x : sym_state)
|Intermediate_Sym_Ex (x : sym_state).*)

(* Symbolic state contains abstract state 
and path constraint. *)
Inductive sym_state: Type :=
|ConstructState (a : Phi) (p : PC)
|SymEx (x : sym_state).


Definition up_pc := PC -> PC.
Axiom update_pc : up_pc.
Definition up_phi := Phi -> Phi.
Axiom update_phi: up_phi.

(* get_phi returns abstract state *)
Fixpoint get_phi (x : sym_state) : Phi :=
match x with
|ConstructState phi pc => phi
|SymEx a => update_phi (get_phi a)
end.

(* get_pc returns the path constraint *)
Fixpoint get_pc (x : sym_state) : PC :=
match x with
|ConstructState phi pc => pc
|SymEx a => update_pc (get_pc a)
end.

Fixpoint sym_ex (A:sym_state) : sym_state:=
match A with 
| ConstructState phi pc => SymEx A
| SymEx a => SymEx (sym_ex a)
end.


(*Class SymExec (pc phi: Type) := {
  get_phi : phi -> Phi ;
  get_pc : pc -> PC;
  update_phi : phi -> Prop;
  update_pc : pc -> Prop;
  cons_state : pc -> phi -> sym_state;
  unif : pc -> phi -> conc_state_set;
  sym_ex : pc -> phi -> sym_state;
  intermediate_sym_ex : phi -> sym_state}.*)


Fixpoint sym_ex_n (x:sym_state) (n:nat) : sym_state :=
match n with
|0 => x
|S n' => sym_ex (sym_ex_n x (n'))
end.


(* unif(A) returns the set of concrete states
 represented by symbolic state A. *)
(* Not convinced that this is saying what I want it to. 
I think it's returning the entire set of conc states, not just a subset.*)
(*Definition unif (A:sym_state) : ConcState.conc_state_set :=
match A with 
| sym_state => ConcState.conc_state_set
end.*)

Definition uni := sym_state -> ConcState.conc_state_set.
Axiom unif : uni.

(* is_leaf(T, n) returns true if
 n is a leaf in tree T. *)
(* is_root(T, n) returns true if
 n is a root in tree T. *)
(* get_root(T) returns the root of tree T. *)
(*Modified version of FSet RBT https://github.com/coq-contribs/fsets/blob/master/FSetRBT.v *)
Definition state := SymbolicExec.sym_state.

Inductive SE_tree : Type :=
| leaf: SE_tree
| sym_node: SE_tree -> state -> SE_tree -> SE_tree
| intermediate_node : SE_tree -> state ->SE_tree.

Fixpoint max (m n : nat) : nat :=
match m, n with
|0, _ => n
|S m', 0 => m
|S m', S n' => S (max m' n')
end.

Fixpoint tree_height (t : SE_tree) : nat :=
match t with
|leaf => O
|sym_node l n r  => S (max (tree_height l) (tree_height r))
|intermediate_node child n => S (tree_height child)
end.

Inductive SE_tree_list : Type :=
|nil: SE_tree_list
|cons: SE_tree -> SE_tree_list -> SE_tree_list.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint length (l:SE_tree_list) : nat := 
  match l with
  | nil => O
  | h :: t => S (length t)
  end.


Fixpoint in_tree_list  (tlist : SE_tree_list) (x : SymbolicExec.SE_tree) : Prop :=
match tlist with 
|nil => False
|h :: t => (x = h) \/ (in_tree_list t x)
end.




Definition is_leaf (T: SE_tree) (n : SymbolicExec.sym_state) : Prop := True.



(* SE Properties Go Here *)
Axiom lem_1 : forall (conc1 conc2 : ConcState.conc_state)
 (sym1: SymbolicExec.sym_state),
(conc_ex conc1 = conc2) /\ (In (unif sym1) conc1)  ->
exists sym2, 
(In (unif sym2) conc2) /\ sym_ex sym1 = sym2. 

Axiom lem_1_n : forall (conc1 conc2 : ConcState.conc_state)
 (sym1: SymbolicExec.sym_state) (n : nat),
(conc_ex_n conc1 n = conc2) /\ (In (unif sym1) conc1)  ->
exists sym2, 
(In (unif sym2) conc2) /\ sym_ex_n sym1 n = sym2.

Axiom lem_2 : forall (conc2 : ConcState.conc_state)
 (sym1 sym2: SymbolicExec.sym_state),
(sym_ex sym1 = sym2) /\ (In (unif sym2) conc2)  ->
exists conc1, 
(In (unif sym1) conc1) /\ 
(conc_ex conc1 = conc2).

Axiom lem_2_n : forall (conc2 : ConcState.conc_state)
 (sym1 sym2: SymbolicExec.sym_state) (n:nat),
(sym_ex_n sym1 n = sym2) /\ (In (unif sym2) conc2)  ->
exists conc1, 
(In (unif sym1) conc1) /\ 
(conc_ex_n conc1 n = conc2).








End SymbolicExec.


Import SymbolicExec. 


Module SymbolicExecList. 



End SymbolicExecList.

Import SymbolicExecList.

Module SERecurs.


Definition circle_op_1 (sym : SymbolicExec.sym_state) : ConcState.conc_state_set :=
unif sym.

Definition circle_op_2 (sym : SymbolicExec.sym_state) : ConcState.conc_state_set :=
unif (sym_ex sym).

Fixpoint set_in_set (set1 set2 : ConcState.conc_state_set) : Prop :=
match set1 with 
|Empty => (set2 = Empty) \/ False
|Cons y s => (set1 = set2) \/ (set_in_set s set2)
end.

Variable init_conc_states: ConcState.conc_state_set.

(* 3 properties and sufficiency go here *)
Variable ErrorStates: ConcState.conc_state_set.

Variable tree_list : SymbolicExec.SE_tree_list.
(* NEED TREE LIST GENERATION *)


Definition is_connected (tlist : SymbolicExec.SE_tree_list) : Prop := True.


Axiom properties : forall (e : SymbolicExec.SE_tree), 
in_tree_list tree_list e -> 
exists n,
(SymbolicExec.is_leaf e n)
/\(set_in_set init_conc_states  (circle_op_1 n))
/\ (set_in_set  ErrorStates (circle_op_2 n))
/\ (is_connected tree_list). 

End SERecurs.



(*Fixpoint list_size (l : input_list) : nat :=
match l with
|EmptyList => 0
|ConsList head last_elem => 1 + list_size last_elem
end.
*)

(*



Fixpoint in_tree_list  (tlist : SE_tree_list) (x : SE_tree) : Prop :=
match tlist with 
|nil => False
|h :: t => (x = h) \/ (in_tree_list t x)
end.*)

(*Fixpoint is_connected  (tlist : SE_tree_list) : Prop :=
 match tlist with
|nil => True
|h :: t => (is_leaf_state (last_elem h) (root t)) /\ is_connected h
end.*)

(*
(* SE Properties Go Here *)
Axiom lem_1 : forall (conc1 conc2 : ConcState.conc_state) (inp1 : ConcState.input)
 (sym1: SymbolicExec.sym_state),
(conc_ex (singleton conc1) inp1 = (singleton conc2)) /\ (In ConcState.conc_state (concretize (get_phi sym1) (get_pc sym1)) conc1)  ->
exists sym2, 
(In ConcState.conc_state (concretize (get_phi sym2) (get_pc sym2)) conc2) /\ 
((left_child (sym_ex_with_branching sym1)) = sym2) \/ ((right_child (sym_ex_with_branching sym1)) = sym2). 

Axiom lem_1_n : forall (conc1 conc2 : ConcState.conc_state) (inp1 : ConcState.input_list)
 (sym1: SymbolicExec.sym_state) (n : nat),
(list_size inp1 = n)/\(conc_ex_input_list (singleton conc1) inp1 = (singleton conc2)) /\ (In ConcState.conc_state (concretize (get_phi sym1) (get_pc sym1)) conc1)  ->
exists sym2, 
(In  ConcState.conc_state (concretize (get_phi sym2) (get_pc sym2)) conc2) /\ (in_tree (sym_ex_n_with_branching sym1 n) sym2).

Axiom lem_2 : forall (conc2 : ConcState.conc_state) (inp1 : ConcState.input)
 (sym1 sym2: SymbolicExec.sym_state),
(in_tree (sym_ex_with_branching sym1) sym2) /\ (In ConcState.conc_state (concretize (get_phi sym2) (get_pc sym2)) conc2)  ->
exists conc1, 
(In ConcState.conc_state (concretize (get_phi sym1) (get_pc sym1)) conc1) /\ 
((conc_ex (singleton conc1) inp1) = (singleton conc2)).

Axiom lem_2_n : forall (conc2 : ConcState.conc_state)
 (sym1 sym2: SymbolicExec.sym_state) (n:nat),
(in_tree (sym_ex_n_with_branching sym1 n) sym2) /\ (In ConcState.conc_state (concretize (get_phi sym2) (get_pc sym2)) conc2)  ->
exists conc1, exists inp1,
(list_size inp1 = n) /\
(In ConcState.conc_state (concretize (get_phi sym1) (get_pc sym1)) conc1) /\ 
(conc_ex_input_list (singleton conc1) inp1 = (singleton conc2)).*)

(*Definition etl1 (tlist: SE_tree_list) (init_s: Ensemble ConcState.conc_state) : Ensemble ConcState.conc_state :=
conc_ex init_s second_elem tlist.

Fixpoint etl2 (tlist : SE_tree_list) (init_s: Ensemble ConcState.conc_state) : Ensemble ConcState.conc_state :=
match tlist with
|nil => Singleton ConcState.conc_state EmptyState
|h::t => 
  match t with 
  |nil => elt1 tlist init_s
  |th::tlast_elem => etl2 t (conc_ex get_input((get_pc (root (second_elem tlist))))*)

(*Fixpoint execute_tree_list2 (tlist : SE_tree_list)  (cs : Ensemble ConcState.conc_state)  : Ensemble ConcState.conc_state :=
match tlist with 
|nil => Singleton ConcState.conc_state EmptyState
|h :: t => 
  match t with
  |nil => cs
  |thead :: tlast_elem => 
    execute_tree_list2 
    t 
    (conc_ex cs (get_input (get_pc (root (second_elem tlist)))))
  end
end.*)

(*
Fixpoint etl_counter (tlist: SE_tree_list) (n:nat) (cs : Ensemble ConcState.conc_state) : Ensemble ConcState.conc_state:=
match n, tlist with
|S n, nil => Singleton ConcState.conc_state EmptyState
|0, h::t => Singleton ConcState.conc_state EmptyState
|0, nil => cs
|S n, h::t => etl_counter t n (conc_ex cs (get_input (get_pc (root (second_elem tlist))))) 
end.


*)


Inductive Sym_state_list : Type :=
|nil_list: Sym_state_list
|sscons: sym_state -> Sym_state_list -> Sym_state_list.

(*This axiom states that these error states can be reached through normal concrete execution*)
(*Axiom error_reachability:
forall (state : ConcState.conc_state),
(In ConcState.conc_state ErrorStates state) ->
exists (ilist: ConcState.input_list),
(In ConcState.conc_state 
(conc_ex_input_list init_conc_states ilist) state).*)


(*Axiom falsest : forall (x: ConcState.conc_state), 
In ConcState.conc_state (Empty_set ConcState.conc_state) x -> 
x = EmptyState.


Axiom conc_inc: forall (state1 state2 : Ensemble ConcState.conc_state) (i : ConcState.input),
Included ConcState.conc_state state1 state2 ->
Included ConcState.conc_state (conc_ex state1 i) (conc_ex state2 i).



Axiom sub1: forall s: SE_tree,
Intersection conc_state
  (conc_ex init_conc_states
     (get_input (get_pc (root s))))
  ErrorStates <> Empty_set conc_state. *)

(*Axiom concretization: forall s : sym_state, concretize (get_phi s) (get_pc s) = Singleton ConsState (get_input (get_pc s)) (get_state (get_phi s)).*)



(*Axiom concretize_elim: *)

(*Axiom elt_ax_init: 
execute_tree_list tree_list = conc_ex (execute_tree_list (tail tree_list)).
*)

(*Axiom basecase2: forall s: SE_tree, init_conc_states = circle_op_2 (root s).
*)

Axiom done2: forall tlist : SE_tree_list,
is_connected tlist ->
match tlist with
|nil => True
|nil :: t => True
|h :: t => conc_ex (circle_op_2 (root (last_elem h))) (get_input (get_pc (root t))) = circle_op_2 (root t)
end.

Axiom done3: forall tlist : SE_tree_list,
is_connected tlist ->
 conc_ex (circle_op_2 (root (second_last_elem tlist))) (get_input (get_pc (root (last_elem tlist)))) = circle_op_2 (root (last_elem tlist)).

Axiom cio: is_consecutive_in_order (second_last_elem tree_list) (last_elem tree_list) tree_list.

Axiom sle : forall (s : SE_tree_list) (s1 s0: SE_tree),
(second_last_elem ((s :: s1) :: s0)) = last_elem (s :: s1).

Axiom cio_sle: forall (s : SE_tree_list) (s1 s0: SE_tree),
tree_list = ((s :: s1) :: s0) ->
is_consecutive_in_order 
(last_elem(s :: s1))
 (last_elem ((s :: s1) :: s0))
 tree_list.

(*Axiom bc3: forall s0: SE_tree, conc_ex init_conc_states (get_input (get_pc (root s0))) =
circle_op_2 (root s0).*)



(*Fixpoint in_tree (tree: SE_tree) (state : sym_state) : Prop :=
match tree with
|leaf => False
|ConsNode l n r => 
(in_tree l state)\/
(n = state) \/
(in_tree r state)
end.*)

(*
Definition get_st := Phi -> ConcState.state.
Axiom get_state : get_st.*)

(*

Definition left_child (tree : SE_tree) : sym_state :=
match tree with 
|leaf => nilstate
|ConsNode l n r => root l
end.

Definition right_child (tree : SE_tree) : sym_state :=
match tree with 
|leaf => nilstate
|ConsNode l n r => root r
end.


Definition sym_ex_with_branching (state : sym_state) : SE_tree :=
match state with 
|ConstructState phi pc => 
ConsNode 
(ConsNode leaf (ConstructState (update_phi_left phi ) (update_pc_left pc)) leaf)
 state
(ConsNode leaf (ConstructState (update_phi_right phi ) (update_pc_right pc)) leaf)
|nilstate => leaf
end.


Fixpoint sym_ex_n_with_branching (state : sym_state) (n:nat) : SE_tree :=
match n with
|0 => sym_ex_with_branching state
|S n' => ConsNode 
(sym_ex_n_with_branching (left_child (sym_ex_with_branching state)) n')
state
(sym_ex_n_with_branching (right_child (sym_ex_with_branching state)) n')
end. *)

(*Definition tail (tlist : SE_tree_list) : SE_tree_list :=
match tlist with
|nil => nil
|h::nil => nil
|h::t => t
end.*)


(*Fixpoint is_consecutive_in_order_2 (A B : SE_tree) (tlist : SE_tree_list) : Prop :=
match tlist with 
|nil => False
|h :: t => 
  match h with
  |nil => False
  |newh :: newt => ((A = newt) /\  (B = t)) 
  \/ (is_consecutive_in_order A B h)
  end
end.*)

(*
Axiom is_connected_app: 
forall (tlist : SE_tree_list),
is_connected tlist ->
is_leaf_state (second_last_elem tlist) (root (last_elem tlist)).


*)
(*
Axiom circle_op_switch : forall (s0 s1: sym_state), 
conc_ex (circle_op_1 s1 s0) (get_input (get_pc s0))
= conc_ex (circle_op_2 s1) (get_input (get_pc s0)).*)



(*
Axiom empt : [ ] = [ ] :: leaf. 


Theorem tlist_structure : forall t : SE_tree_list,
t = (headlist t)::(last_elem t).
Proof.
induction t.
-simpl. apply empt.
-simpl. auto. Qed.*)

(*

Theorem tree_list_struct : 
tree_list = headlist tree_list :: last_elem tree_list.
Proof. apply tlist_structure. Qed.
*)

(*Axiom cio : forall (tl tl2 : SE_tree_list) (a b : SE_tree),
tl2 = ((tl :: a ) :: b) ->
is_consecutive_in_order a b tl2.*)

(*
Theorem tlist_size_1_mod:
forall (s: SE_tree),
size ([ ] :: s) = 1.
Proof. intros. simpl;auto. Qed. *)



(*Theorem etl_size_gt1:
forall (tlist : SE_tree_list) (s t : SE_tree),
(size tlist) > 1 ->
execute_tree_list (tlist :: t) =
conc_ex 
(execute_tree_list tlist)
(get_input (get_pc  (root t))).
Proof. intros.
destruct tlist.
-inversion H.
-destruct tlist.
*pose tlist_size_1_mod. inversion H. inversion H1.
*simpl;auto. Qed.*)


(*
Theorem etl_empty: 
forall tlist : SE_tree_list,
(size tlist) = 0 ->
execute_tree_list tlist = Singleton ConcState.conc_state EmptyState.
Proof. intros. induction tlist.
-simpl; auto.
-pose H as H1. rewrite tlist_size in H1. simpl in H1. 
pose tlist_size_geq_0 as z. simpl in H. pose gt_Sn_O. inversion H.
Qed.
*)

(*
Theorem etl_size_1: 
forall tlist : SE_tree_list,
(size tlist) = 1 ->
execute_tree_list tlist = Singleton ConcState.conc_state EmptyState.
Proof. intros. induction tlist.
-simpl; auto.
-apply tlist_size_1 in H. rewrite H. simpl;auto.
Qed.*)



(*
Theorem tlist_size_geq_0: 
forall (tlist: SE_tree_list) (s: SE_tree),
size (tlist :: s) >= 0.
Proof. intros. induction tlist.
-simpl;auto.
-rewrite tlist_size in IHtlist. simpl; auto.
Qed. *)
(*
Theorem tlist_size_0:
forall (tlist: SE_tree_list) (s: SE_tree),
tlist = [] ->
size (tlist) = 0.
Proof. intros. induction tlist.
-simpl;auto.
-simpl; auto. inversion H. Qed.*)
(*
Theorem tlist_size_1:
forall (tlist: SE_tree_list) (s: SE_tree),
size (tlist::s) = 1 ->
tlist = [].
Proof. intros.
induction tlist.
-auto.
-simpl in H. inversion H. Qed. *)

(*Necessary?*)
(*Axiom error_include_empty: In conc_state ErrorStates EmptyState.
*)
(*
Definition up_pc_l := PC -> PC.
Axiom update_pc_left : up_pc_l.

Definition up_pc_r := PC -> PC.
Axiom update_pc_right : up_pc_r.

Definition up_phi_l := Phi -> Phi.
Axiom update_phi_left: up_phi_l.

Definition up_phi_r := Phi -> Phi.
Axiom update_phi_right: up_phi_r.*)
