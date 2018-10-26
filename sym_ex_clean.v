

Module ConcState.

Variable input : Type.

Inductive input_list : Type :=
|EmptyList
|ConsList (i : input) (s : input_list).

Fixpoint in_input_list (l : input_list) (i : input) : Prop :=
match l with
|EmptyList => False
|ConsList item i_list => (item = i) \/ (in_input_list i_list i)
end . 


Inductive conc_state : Type :=
|concstate.


Inductive conc_state_set : Type :=
|Empty 
|Cons (x : conc_state) (s: conc_state_set).

(* conc_ex(A) returns ConcState that results from 
the concrete execution of ConcState A  *)
Definition concrete_execution := conc_state_set -> input -> conc_state_set.

Axiom conc_ex : concrete_execution.


Fixpoint In (A : conc_state_set) (x : conc_state) : Prop := 
match A with 
|Empty => False
|Cons y s => (y=x) \/ In s x
end.

(* Returns True is set2 is subset of set1 *)
Fixpoint is_subset (set1 set2 : conc_state_set) : Prop :=
match set2 with 
|Empty => True
|Cons y s => (In set1 y) /\ (is_subset set1 s)
end.

(*Inductive intersection (B C: conc_state_set) : conc_state_set :=
    Intersection_intro :
    forall x : conc_state, In B x -> In C x -> In (intersection B C) x.*)
Definition intn := conc_state_set -> conc_state_set -> conc_state_set.

Axiom intersection : intn.


End ConcState.

Import ConcState.



Module System.
(* System initializes with a defined set of
 initial configuration states, InitStates *)



(*Fixpoint conc_ex_n (x: ConcState.conc_state) (n:nat) : ConcState.conc_state_set :=
match n with
|0 => Cons x Empty
|S n' => conc_ex (conc_ex_n x (n'))
end.*)

End System.

Import System. 

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

Definition sym_execution := sym_state -> sym_state.
Axiom sym_ex : sym_execution.

(*Fixpoint sym_ex_n (x:sym_state) (n:nat) : sym_state :=
match n with
|0 => x
|S n' => sym_ex (sym_ex_n x (n'))
end.
*)

Definition uni := Phi -> PC -> ConcState.conc_state_set.
Axiom unif : uni.



Inductive SE_tree : Type :=
| leaf: SE_tree
| ConsNode: SE_tree -> sym_state -> SE_tree -> SE_tree.

Definition root (t : SE_tree) : sym_state :=
match t with 
|leaf => nilstate
|ConsNode l n r => n
end.

(*Fixpoint tree_height (t : SE_tree) : nat :=
match t with
|leaf => O
|ConsNode l n r  => S (max (tree_height l) (tree_height r))
end.
*)

Fixpoint is_leaf_state (tree : SE_tree) (state : sym_state) : Prop :=
match tree with 
|leaf => False
|ConsNode l n r => 
  ((n = state) /\ (l = leaf))
  \/ (is_leaf_state l state)
  \/ (is_leaf_state r state)
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




Fixpoint in_tree_list  (tlist : SE_tree_list) (x : SE_tree) : Prop :=
match tlist with 
|nil => False
|h :: t => (x = h) \/ (in_tree_list t x)
end.

Definition head (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|h :: t => h
end.

Definition second_elem (tlist : SE_tree_list) : SE_tree :=
match tlist with
|nil => leaf
|h :: t => (head t)
end.

Fixpoint tail (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|h :: t => 
  match t with
  |nil => h
  |tailh :: tailt => tail t
  end
end.

(*is_consecutive_in_order checks if A and B are consecutive in the tree list
and if A comes before B *)
Fixpoint is_consecutive_in_order (A B : SE_tree) (tlist : SE_tree_list) : Prop :=
match tlist with 
|nil => False
|h :: t => 
  ((A = h) /\  (B = (head t))) 
  \/ (is_consecutive_in_order A B t)
end.



Definition is_connected  (tlist : SE_tree_list) : Prop :=
 forall (A B : SE_tree), 
 (is_consecutive_in_order A B tlist) ->
  is_leaf_state A (root B). 

Inductive Sym_state_list : Type :=
|nil_list: Sym_state_list
|sscons: sym_state -> Sym_state_list -> Sym_state_list.

(*Notation "x :: l" := (sscons x l) (at level 60, right associativity).
Notation "[ ]" := endstate.
Notation "[ x ; .. ; y ]" := (sscons x .. (sscons y nil) ..).*)


Fixpoint list_of_leaf_states (tlist : SE_tree_list) : Sym_state_list:=
match tlist with
|nil => nil_list
|h :: t => 
  match t with 
    |nil => nil_list
    |headt :: tailt => sscons (root (head t)) (list_of_leaf_states t)
  end
end.

Fixpoint remove_tail (slist : Sym_state_list) : Sym_state_list :=
match slist with 
|nil_list => nil_list
|sscons h t => 
  match t with
  |nil_list => nil_list
  |sscons headt tailt => sscons h (remove_tail t) 
  end
end.

(*Fixpoint state_list_execution (slist : Sym_state_list) : conc_state_set :=
match slist with
|nil_list => Empty 
|sscons h t => 
  match t with 
  |nil_list => conc_ex (unif h)
  |sscons headt tailt => conc_ex (state_list_execution (remove_tail slist))
  end
end.*)




(*
(* SE Properties Go Here *)
Axiom lem_1 : forall (conc1 conc2 : ConcState.conc_state)
 (sym1: SymbolicExec.sym_state),
(conc_ex (Cons conc1 Empty) = (Cons conc2 Empty)) /\ (In (unif (get_phi sym1) (get_pc sym1)) conc1)  ->
exists sym2, 
(In (unif (get_phi sym2) (get_pc sym2)) conc2) /\ sym_ex sym1 = sym2. 

Axiom lem_1_n : forall (conc1 conc2 : ConcState.conc_state)
 (sym1: SymbolicExec.sym_state) (n : nat),
(conc_ex_n conc1 n = (Cons conc2 Empty)) /\ (In (unif (get_phi sym1) (get_pc sym1)) conc1)  ->
exists sym2, 
(In (unif (get_phi sym2) (get_pc sym2)) conc2) /\ sym_ex_n sym1 n = sym2.

Axiom lem_2 : forall (conc2 : ConcState.conc_state)
 (sym1 sym2: SymbolicExec.sym_state),
(sym_ex sym1 = sym2) /\ (In (unif (get_phi sym2) (get_pc sym2)) conc2)  ->
exists conc1, 
(In (unif (get_phi sym1) (get_pc sym1)) conc1) /\ 
((conc_ex (Cons conc1 Empty)) = (Cons conc2 Empty)).

Axiom lem_2_n : forall (conc2 : ConcState.conc_state)
 (sym1 sym2: SymbolicExec.sym_state) (n:nat),
(sym_ex_n sym1 n = sym2) /\ (In (unif (get_phi sym2) (get_pc sym2)) conc2)  ->
exists conc1, 
(In (unif (get_phi sym1) (get_pc sym1)) conc1) /\ 
(conc_ex_n conc1 n = (Cons conc2 Empty)).


*)





End SymbolicExec.


Import SymbolicExec. 



Module SERecurs.

(* Takes as input symbolic state of root and pc of its leaf 
and returns all and only the concrete states that will take us down 
the path that leads to the leaf. *)
Definition circle_op_1 (sym sym_leaf : SymbolicExec.sym_state) : ConcState.conc_state_set :=
unif (get_phi sym) (get_pc sym_leaf).

(*Takes as input symbolic state of leaf state and pc of leaf state 
and returns concrete states that correspond *)
Definition circle_op_2 (sym : SymbolicExec.sym_state) : ConcState.conc_state_set :=
unif (get_phi (sym_ex sym)) (get_pc (sym_ex sym)).






Variable init_conc_states: ConcState.conc_state_set.


Variable ErrorStates: ConcState.conc_state_set.

Variable tree_list : SymbolicExec.SE_tree_list.






Axiom properties : 
(is_subset init_conc_states  (circle_op_1 (root (head tree_list))))
/\ (is_subset  ErrorStates (circle_op_2 (root (tail tree_list))))
/\ (is_connected tree_list). 


(*
Theorem sufficiency : forall (tree : SE_tree), 
tree*)



(*
Axiom x : forall (s : SE_tree_list) (a b : SE_tree),
is_consecutive_in_order (last_elem (s :: a)) (last_elem ((s:: a)::b))  ((s:: a)::b).
*)
(*
Theorem paren_elim : 
forall x y : SE_tree,
(([ ] :: x) :: y)  = (x :: y).*)

(*execute_tree_list (([ ] :: x) :: y) =*)
(*
Axiom leaf_co_unif:
forall (t: SE_tree) (l: sym_state),
(is_leaf_state t l) ->
Included ConcState.conc_state 
(circle_op_2 (root t)) (circle_op_1 (root t) l).

Axiom etl_help:
forall x y : SE_tree,
size (([] :: x ):: y) = 2 ->
(execute_tree_list (([] :: x ):: y))
= conc_ex
  (conc_ex init_conc_states
     (get_input (get_pc (root x))))
  (get_input (get_pc (root y))).


Axiom etl_help2:
forall x y : SE_tree,
size (([] :: x ):: y) = 2 ->
(execute_tree_list (([] :: x ):: y))
= conc_ex
  (conc_ex init_conc_states
     (get_input (get_pc (root x))))
  (get_input (get_pc (root y))).

*)

(*
Axiom co2_leaf: 
forall (t: SE_tree) (l: sym_state),
is_leaf_state t l ->
conc_ex (circle_op_2 (root t))
  (get_input (get_pc l)) = circle_op_2 l.*)

(*(*Necessary?*)
Axiom tlist_non_empty: (tree_list <> nil).



Axiom basecase: Singleton conc_state EmptyState =
circle_op_2 nilstate.


Axiom bc2: forall s0: SE_tree, conc_ex
  (Singleton conc_state EmptyState)
  (get_input (get_pc (root s0))) =
circle_op_2 (root s0).


Axiom unif: 
conc_ex 
init_conc_states 
(get_input(get_pc (root (second_elem tree_list))))
= circle_op_2 (root(second_elem tree_list)).


(*NEEDS TO BE PROVEN*)
Axiom connected_conc: 
forall s0 s1 : SE_tree,
is_consecutive_in_order s0 s1 tree_list ->
conc_ex (circle_op_2 (root s0))
  (get_input (get_pc (root s1))) =
circle_op_2 (root s1).


Axiom ch : forall (tlist : SE_tree_list) (s0 : SE_tree),
conc_ex (execute_tree_list (tlist))
  (get_input (get_pc (root s0))) =
circle_op_2
  (root (last_elem (tlist :: s0))).

Axiom dks : forall (s0 s1 : SE_tree),
is_consecutive_in_order_2 s1 s0 tree_list -> 
conc_ex (circle_op_2 (root s1))
  (get_input (get_pc (root s0))) =
circle_op_2 (root s0).

Axiom last_2_elem: forall (s1 s0: SE_tree) (tl: SE_tree_list), 
second_last_elem tl = s1 /\ last_elem tl = s0
-> is_consecutive_in_order_2 s1 s0 tl.

Axiom base: forall s0: SE_tree, Singleton conc_state EmptyState =
circle_op_2 (root s0).

Axiom co_unif : forall (s: SE_tree_list) (s0 s1 : SE_tree),
 is_connected ((s :: s1) :: s0) -> 
conc_ex (circle_op_1 (root s1) (root s0)) (get_input (get_pc (root s0))) 
= circle_op_2 (root s0).

Axiom p1_alt: forall s0 s1 : SE_tree,
conc_ex init_conc_states
  (get_input (get_pc (root s0))) =
conc_ex (circle_op_1 (root s1) (root s0))
  (get_input (get_pc (root s0))).

Axiom leaf_eq : forall (A B : SE_tree), 
is_leaf_state A (root B) ->
circle_op_2 (root B) = 
conc_ex (circle_op_1 (root A) (root B))
  (get_input (get_pc (root B))).

Axiom etl_elim : forall (s: SE_tree_list) (s0 : SE_tree),
is_connected (s::s0) ->
execute_tree_list (s::s0) = 
conc_ex (execute_tree_list s) (get_input (get_pc(root s0))).

Axiom connection : forall (d: SE_tree_list) (a b c : SE_tree),
is_connected (((d :: a) :: b) :: c) -> is_connected ((d :: a) :: b).


Axiom p1 : forall (s: SE_tree_list) (s0 s1 : SE_tree),
 is_connected ((s :: s1) :: s0) -> 
execute_tree_list ((s :: s1) :: s0) =
conc_ex (circle_op_1 (root s1) (root s0))
  (get_input (get_pc (root s0))).

Axiom bcbc: forall s0:SE_tree, conc_ex init_conc_states
  (get_input (get_pc (root s0))) =
circle_op_2 (root s0).

Axiom co2_unif: 
forall (t : SE_tree) (s : sym_state),
is_leaf_state t s ->
circle_op_2 (root t) s


Theorem x : forall (s : SE_tree_list) (s0: SE_tree), 
is_connected (s :: s0)
/\ (size s >0 ) ->
execute_tree_list (s :: s0) =
circle_op_2 (root s0).
Proof. intros. induction s.
-inversion H. inversion H1.
-destruct s.
*simpl. unfold circle_op_2. rewrite etl_size_1.

 rewrite etl_main. rewrite etl_main in IHs. rewrite etl_main. rewrite <- IHs.  pose H as H2. apply y in H2. 

 rewrite <- H2. rewrite circle_op_unif. apply p1; auto. Qed.*)
(*
Axiom circle_op_unification: 
forall (t : SE_tree) (s : sym_state),
is_leaf_state t s ->
(circle_op_1 (root t) s)
= conc_ex (circle_op_2 (root t)) (get_input (get_pc s)).
*)


(*

Axiom basecase : Singleton conc_state EmptyState = circle_op_2 nilstate.

Axiom size1: forall tl : SE_tree_list,
size tl = 1 ->
execute_tree_list tl = circle_op_2 (root (last_elem tl)).*)



(*
Axiom conc_ex_empty: forall i : ConcState.input,
conc_ex (Singleton conc_state EmptyState) i = Singleton conc_state EmptyState.
*)
(*
Theorem etl_main : forall (s: SE_tree_list) (s1 : SE_tree),  
execute_tree_list(s::s1) = conc_ex (execute_tree_list s) (get_input (get_pc  (root s1))).
Proof.
intros tlist tail.
induction tlist.
-simpl. rewrite conc_ex_empty. reflexivity.
-induction tlist.
*simpl. rewrite conc_ex_empty2. reflexivity.
*auto. Qed.
*)




(*
Theorem etl_size_gt2:
forall (tlist : SE_tree_list) (s t : SE_tree),
(size tlist) > 1 ->
execute_tree_list ((tlist :: s) :: t) =
conc_ex
(conc_ex 
(Singleton conc_state EmptyState)
(get_input (get_pc (root s))))
(get_input (get_pc (root t))).
Proof. intros.
destruct tlist.
-inversion H.
-destruct tlist.
*simpl; auto.
simpl.*)




(*Theorem etl_size2:
forall tlist : SE_tree_list,
(size tlist) = 2 ->
 execute_tree_list tlist = 
conc_ex (conc_ex init_conc_states (get_input (get_pc (root s)))) (get_input (get_pc  (root t))).
Proof. intros. destruct tlist.
-inversion H.
-destruct tlist.
*simpl in H. inversion H.
*simpl in H. destruct tlist.
+simpl; auto.
+simpl in H. inversion H. Qed.*)

(*Theorem etl_size2_modified:
forall (tlist : SE_tree_list) (s : SE_tree),
(size tlist) = 1 ->
 execute_tree_list (tlist :: s) = 
conc_ex init_conc_states (get_input (get_pc (root s))).
Proof. intros. destruct tlist.
-inversion H.
-apply tlist_size_1 in H. rewrite H. simpl;auto. Qed.*)
End SERecurs.


