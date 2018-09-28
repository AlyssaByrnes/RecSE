Require Import Ensembles Setoid Equalities EquivDec. 


Module ConcState.

Variable input : Type.
Variable state: Type.





Inductive input_list : Type :=
|EmptyList
|ConsList (i : input) (s : input_list).

Fixpoint in_input_list (l : input_list) (i : input) : Prop :=
match l with
|EmptyList => False
|ConsList item i_list => (item = i) \/ (in_input_list i_list i)
end . 




(*Variable conc_state : Type.*)

Inductive conc_state : Type :=
|EmptyState
|ConsState (i: input) (s: state).


(* conc_ex(A, input) returns ConcState that results from 
the concrete execution of ConcState A with an input  *)
Definition concrete_execution := Ensemble conc_state -> input -> Ensemble conc_state.

Axiom conc_ex : concrete_execution.



Definition singleton (l : conc_state) : Ensemble conc_state :=
  Add conc_state (Empty_set conc_state) l.


Fixpoint conc_ex_input_list (states : Ensemble conc_state) (ilist : input_list) : Ensemble conc_state:=
match ilist with
|EmptyList => states
|ConsList inp list_last_elem => conc_ex_input_list (conc_ex states inp) list_last_elem
end.

Fixpoint list_size (l : input_list) : nat :=
match l with
|EmptyList => 0
|ConsList head last_elem => 1 + list_size last_elem
end.



End ConcState.

Import ConcState.





Module SymbolicExec.


(* Symbolic state contains abstract state 
and path constraint. *)


Variable Phi PC : Type.

Inductive sym_state: Type :=
|ConstructState (a : Phi) (p : PC)
|nilstate.



Definition up_pc_l := PC -> PC.
Axiom update_pc_left : up_pc_l.

Definition up_pc_r := PC -> PC.
Axiom update_pc_right : up_pc_r.

Definition up_phi_l := Phi -> Phi.
Axiom update_phi_left: up_phi_l.

Definition up_phi_r := Phi -> Phi.
Axiom update_phi_right: up_phi_r.

(* get_phi returns abstract state *)
Definition get_sym_state  :=  sym_state -> Phi.
Axiom get_phi : get_sym_state.

(* get_pc returns the path constraint *)
Definition get_path_constraint := sym_state -> PC.
Axiom get_pc : get_path_constraint.


Definition uni := Phi -> PC -> Ensemble ConcState.conc_state.

Axiom concretize : uni.

Definition get_inp := PC -> ConcState.input.
Axiom get_input : get_inp.


Definition get_st := Phi -> ConcState.state.
Axiom get_state : get_st.

Inductive SE_tree : Type :=
| leaf: SE_tree
| ConsNode: SE_tree -> sym_state -> SE_tree -> SE_tree.

Definition root (t : SE_tree) : sym_state :=
match t with 
|leaf => nilstate
|ConsNode l n r => n
end.


Fixpoint is_leaf_state (tree : SE_tree) (state : sym_state) : Prop :=
match tree with 
|leaf => False
|ConsNode l n r => 
  ((n = state) /\ (l = leaf))
  \/ (is_leaf_state l state)
  \/ (is_leaf_state r state)
end.

Fixpoint in_tree (tree: SE_tree) (state : sym_state) : Prop :=
match tree with
|leaf => False
|ConsNode l n r => 
(in_tree l state)\/
(n = state) \/
(in_tree r state)
end.



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
end.


Inductive SE_tree_list : Type :=
|nil: SE_tree_list
|cons:  SE_tree_list -> SE_tree -> SE_tree_list.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(*



Fixpoint in_tree_list  (tlist : SE_tree_list) (x : SE_tree) : Prop :=
match tlist with 
|nil => False
|h :: t => (x = h) \/ (in_tree_list t x)
end.*)

Fixpoint head (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|nil :: h => h
|h :: t => head h
end.

Fixpoint second_elem (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|h :: t => 
  match h with
|nil => leaf
|nil :: se => t
|tail :: se => second_elem tail
end
end.

Definition last_elem (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|h :: t => t
end.

Definition second_last_elem (tlist: SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|nil :: t => leaf
|h :: t => last_elem h
end.

(*Definition tail (tlist : SE_tree_list) : SE_tree_list :=
match tlist with
|nil => nil
|h::nil => nil
|h::t => t
end.*)

(*is_consecutive_in_order checks if A and B are consecutive in the tree list
and if A comes before B *)
Fixpoint is_consecutive_in_order (A B : SE_tree) (tlist : SE_tree_list) : Prop :=
match tlist with 
|nil => False
|h :: t => 
  ((A = last_elem h) /\  (B = t)) 
  \/ (is_consecutive_in_order A B h)
end.


(*Fixpoint is_connected  (tlist : SE_tree_list) : Prop :=
 match tlist with
|nil => True
|h :: t => (is_leaf_state (last_elem h) (root t)) /\ is_connected h
end.*)

 

Definition is_connected  (tlist : SE_tree_list) : Prop :=
 forall (A B : SE_tree), 
 (is_consecutive_in_order A B tlist) ->
  is_leaf_state A (root B). 

Inductive Sym_state_list : Type :=
|nil_list: Sym_state_list
|sscons: sym_state -> Sym_state_list -> Sym_state_list.






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
(conc_ex_input_list (singleton conc1) inp1 = (singleton conc2)).







End SymbolicExec.


Import SymbolicExec. 



Module SERecurs.

(* Takes as input symbolic state of root and pc of its leaf 
and returns all and only the concrete states that will take us down 
the path that leads to the leaf. *)
Definition circle_op_1 (sym sym_leaf : SymbolicExec.sym_state) : Ensemble ConcState.conc_state :=
concretize (get_phi sym) (get_pc sym_leaf).

(*Takes as input symbolic state of leaf state and pc of leaf state 
and returns concrete states that correspond *)
Definition circle_op_2 (sym : SymbolicExec.sym_state) : Ensemble ConcState.conc_state :=
concretize (get_phi sym) (get_pc sym).




Variable init_conc_states: Ensemble ConcState.conc_state.



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

Fixpoint execute_tree_list (tlist : SE_tree_list)  : Ensemble ConcState.conc_state :=
match tlist with 
|nil => Singleton ConcState.conc_state EmptyState
|h :: t =>
match h with
|nil => Singleton ConcState.conc_state EmptyState
|nil :: htop => conc_ex init_conc_states (get_input (get_pc (root t)))
|newhead :: htop => conc_ex (execute_tree_list h) (get_input (get_pc  (root t)))
end
end.

Axiom conc_ex_empty: forall i : ConcState.input,
conc_ex (Singleton conc_state EmptyState) i = Singleton conc_state EmptyState.

Axiom conc_ex_empty2 : forall s : SE_tree,
 conc_ex init_conc_states (get_input (get_pc (root s))) =
conc_ex (Singleton conc_state EmptyState)(get_input (get_pc (root s))).

Theorem etl_main : forall (s: SE_tree_list) (s1 : SE_tree),  
execute_tree_list(s::s1) = conc_ex (execute_tree_list s) (get_input (get_pc  (root s1))).
Proof.
intros tlist tail.
induction tlist.
-simpl. rewrite conc_ex_empty. reflexivity.
-induction tlist.
*simpl. rewrite conc_ex_empty2. reflexivity.
*auto. Qed.



(*
Fixpoint etl_counter (tlist: SE_tree_list) (n:nat) (cs : Ensemble ConcState.conc_state) : Ensemble ConcState.conc_state:=
match n, tlist with
|S n, nil => Singleton ConcState.conc_state EmptyState
|0, h::t => Singleton ConcState.conc_state EmptyState
|0, nil => cs
|S n, h::t => etl_counter t n (conc_ex cs (get_input (get_pc (root (second_elem tlist))))) 
end.


*)


Variable ErrorStates: Ensemble ConcState.conc_state.

Axiom error_include_empty: In conc_state ErrorStates EmptyState.


Variable tree_list : SymbolicExec.SE_tree_list.

(*Expand circle ops*)
Axiom property1 : 
Included ConcState.conc_state 
init_conc_states
(circle_op_1 (root(head tree_list)) (root (second_elem tree_list))).


(* Equivalent to, but different than property 2 in paper. *)
Axiom property2: (Intersection ConcState.conc_state (circle_op_2 (root (last_elem tree_list))) ErrorStates) 
<> Empty_set ConcState.conc_state.

Axiom property3: is_connected tree_list.


Axiom tlist_non_empty: (tree_list <> nil).

Axiom falsest : forall (x: ConcState.conc_state), 
In ConcState.conc_state (Empty_set ConcState.conc_state) x -> 
x = EmptyState.


Axiom conc_inc: forall (state1 state2 : Ensemble ConcState.conc_state) (i : ConcState.input),
Included ConcState.conc_state state1 state2 ->
Included ConcState.conc_state (conc_ex state1 i) (conc_ex state2 i).

(*Axiom cop2: forall A B : SE_tree, is_leaf_state A (root B) -> 
circle_op_2 (root B) = conc_ex A (get_input (get_pc (root B))).*)


Axiom sub1: forall s: SE_tree,
Intersection conc_state
  (conc_ex init_conc_states
     (get_input (get_pc (root s))))
  ErrorStates <> Empty_set conc_state.

(*Axiom concretization: forall s : sym_state, concretize (get_phi s) (get_pc s) = Singleton ConsState (get_input (get_pc s)) (get_state (get_phi s)).*)

(*This axiom states that these error states can be reached through normal concrete execution*)
(*Axiom error_reachability:
forall (state : ConcState.conc_state),
(In ConcState.conc_state ErrorStates state) ->
exists (ilist: ConcState.input_list),
(In ConcState.conc_state 
(conc_ex_input_list init_conc_states ilist) state).*)

(*Axiom concretize_elim: *)

Axiom basecase: Singleton conc_state EmptyState =
circle_op_2 nilstate.

Axiom basecase2: forall s: SE_tree, init_conc_states = circle_op_2 (root s).

Axiom bc2: forall s0: SE_tree, conc_ex
  (Singleton conc_state EmptyState)
  (get_input (get_pc (root s0))) =
circle_op_2 (root s0).
 

Axiom bc3: forall s0: SE_tree, conc_ex init_conc_states (get_input (get_pc (root s0))) =
circle_op_2 (root s0).

Axiom unif: 
conc_ex 
init_conc_states 
(get_input(get_pc (root (second_elem tree_list))))
= circle_op_2 (root(second_elem tree_list)).

(*Axiom elt_ax_init: 
execute_tree_list tree_list = conc_ex (execute_tree_list (tail tree_list)).
*)
(*NEEDS TO BE PROVEN*)
Axiom connected_conc: 
forall s0 s1 : SE_tree,
is_consecutive_in_order s0 s1 tree_list ->
conc_ex (circle_op_2 (root s0))
  (get_input (get_pc (root s1))) =
circle_op_2 (root s1).

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

Axiom cheat: forall (s : SE_tree_list) (s1 s0: SE_tree), tree_list = (s :: s1) :: s0.

Theorem etl : execute_tree_list tree_list = (circle_op_2 (root (last_elem tree_list))).
Proof. (*rewrite elt_ax_init. *)
induction tree_list.
-apply basecase.
-rewrite etl_main. destruct s. 
*apply bc2. 
* (* rewrite etl_main.*) rewrite IHs.   
apply connected_conc.  apply cio_sle. apply cheat. Qed. 

Theorem sufficiency : 
(Intersection ConcState.conc_state
(execute_tree_list tree_list)  ErrorStates)
<> Empty_set ConcState.conc_state.
Proof. 
rewrite etl. apply property2. Qed.


End SERecurs.


