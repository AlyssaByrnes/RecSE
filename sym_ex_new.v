Require Import Ensembles. 

Module ConcState.

Variable input : Type.
Variable state: Type.

Inductive conc_state : Type :=
|EmptyState
|ConsState (i: input) (s: state).

Definition concrete_execution := Ensemble conc_state -> input -> Ensemble conc_state.
Axiom conc_ex : concrete_execution.

End ConcState.
Import ConcState.

Module SymbolicExec.

Variable Phi PC : Type.

Inductive sym_state: Type :=
|ConstructState (a : Phi) (p : PC)
|nilstate.


(*** SYM STATE STRUCTURE ***)

(* get_phi returns abstract state *)
Definition get_sym_state  :=  sym_state -> Phi.
Axiom get_phi : get_sym_state.

(* get_pc returns the path constraint *)
Definition get_path_constraint := sym_state -> PC.
Axiom get_pc : get_path_constraint.

Definition conc := Phi -> PC -> Ensemble ConcState.conc_state.
Axiom concretize : conc.

Definition get_inp := PC -> ConcState.input.
Axiom get_input : get_inp.


(*** SYM EX TREE STRUCTURE ***)
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

(*** TREE LIST STRUCTURE ***)
Inductive SE_tree_list : Type :=
|nil: SE_tree_list
|cons:  SE_tree_list -> SE_tree -> SE_tree_list.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.

Fixpoint first_elem (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|nil :: h => h
|h :: t => first_elem h
end.

Fixpoint last_elem (tlist : SE_tree_list) : SE_tree :=
match tlist with 
|nil => leaf
|h :: leaf => last_elem h
|h :: t => t
end.

Fixpoint is_consecutive_in_order (A B : SE_tree) (tlist : SE_tree_list) : Prop :=
match tlist with 
|nil => False
|h :: t => 
  ((A = last_elem h) /\  (B = t)) 
  \/ (is_consecutive_in_order A B h)
end.

(*** SET OPERATION SHORT HANDS ***)
Definition singleton (x : ConcState.conc_state) : Ensemble ConcState.conc_state :=
Singleton ConcState.conc_state x.

Definition is_subset (x y : Ensemble ConcState.conc_state) : Prop :=
Included ConcState.conc_state x y.

Definition is_element_of (y : Ensemble ConcState.conc_state) (x : ConcState.conc_state) : Prop :=
In ConcState.conc_state y x.

Definition empty_set := Empty_set ConcState.conc_state.

Definition intersection (x y : Ensemble ConcState.conc_state) : Ensemble ConcState.conc_state :=
Intersection ConcState.conc_state x y.

(*** KING PROPERTIES ***)


End SymbolicExec.
Import SymbolicExec. 

Module SERecurs.

Variable init_conc_state: ConcState.conc_state.
Variable Error_States : Ensemble ConcState.conc_state.

Definition fl := SE_tree -> sym_state.
Axiom find_leaf : fl.

(*** CIRCLE OPERATIONS ***)
(* Takes as input symbolic state of root and pc of its leaf 
and returns all and only the concrete states that will take us down 
the path that leads to the leaf. *)
Definition c_o_1 := SymbolicExec.sym_state -> SymbolicExec.sym_state -> Ensemble ConcState.conc_state.
Axiom circle_op_1: c_o_1.

Definition circle_op_2 (sym : SymbolicExec.sym_state) : Ensemble ConcState.conc_state :=
concretize (get_phi sym) (get_pc sym).

(*** PROPERTIES 1-3 ***)
Definition trees_connect (A B : SE_tree) : Prop :=
forall (x y : sym_state),
(is_leaf_state A x) /\ (is_leaf_state B y) ->
Included ConcState.conc_state 
(circle_op_2 x)
(circle_op_1 (root B) y).

Definition is_connected (tlist : SE_tree_list) : Prop :=
forall (A B : SE_tree), 
is_consecutive_in_order A B tlist ->
trees_connect A B.


(*** SUFFICIENCY ***)
(*Fixpoint execute_tree_list*)


