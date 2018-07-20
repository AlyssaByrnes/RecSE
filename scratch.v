(*Inductive sym_state : Set :=
| Empty
| ConsPhi (a : Phi) (l : sym_state)
| ConsPC (p : PC) (l : sym_state).
*)

(*
Inductive sym_components : Set :=
| IsPhi (a : Phi)
| IsPC (p : PC).
*)


(*Coercion IsPhi : Phi >-> sym_components.
Coercion IsPC : PC >-> sym_components.*)

(*Definition Cons_sym_state (f : sym_components) (l : sym_state) : sym_state :=
  match f with
  | IsPhi a => ConsPhi a l
  | IsPC p => ConsPC p l
  end.*)

(*Definition Cons_sym_state (phi: Phi) (pc: PC) : sym_state:=
ConsPhi phi (ConsPC pc Empty).*)

(*Notation "[ ]" := (Nil) (at level 0).
Notation "[ x ;  y ]" := (Cons_sym_state x  (Cons_sym_state y Nil)) (at level 0).

Variable phi : Phi.
Variable pc : PC.

Definition a_sym_state := [ phi ; pc ]. *)

(*Definition get_phi (A : sym_state) : Phi:=
match A with 
| (ConsPhi x (y  => x
end.

Definition get_pc := pc.*)