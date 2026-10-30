(* The library that opaque_unreadable.v loads.  check_opaque_unreadable.sh
   compiles it with [rocq compile -vos] only, so its .vos file holds the
   declarations and no opaque proof: no command that loads the library from
   that file can read the body of [unreadable_proof].  It is not listed in
   _RocqProject.in, so no .vo, which would hold the proofs, is built for it. *)

Lemma unreadable_proof : True.
Proof. exact I. Qed.

(* A transparent constant whose body cites the opaque one. *)
Definition cites_unreadable : True := unreadable_proof.

(* A transparent constant with no opaque dependency: a control. *)
Definition readable_definition : True := I.
