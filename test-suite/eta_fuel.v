(* BET-64 FUEL (EtaFuel, 2026-10-30): the out-of-fuel outcome of the eta checker and its message.

   The eta checker's three recursions (the reduction machine, the conversion, the cofixpoint codomain walk)
   recurse on a fuel ([PCUICFuelEta]) and give a distinct outcome when it is spent. Every entry starts from
   2^62 units, so no graded run can spend it. This file FORCES a small fuel on the machine, whose fuel is a
   parameter of [reduce_stack_fuel], and checks by computation:
   1. fuel 1 on a term that needs five machine steps: the machine answers [None] (out of fuel); fuel 10 on the
      same term: it answers the weak-head normal form;
   2. the checker turns that [None] into the refusal [NotEnoughFuel] (the [reduce_to_*] pattern, then
      [refuse_of_comp]/[check_of_comp] and the [typing_result] coercion), also when the conversion's error
      carries the fuel outcome under another constructor ([conv_error_fuel]);
   3. the printers print it as a refusal for lack of fuel, never as "Type error:" (the plugin's
      [print_env_error], used by [infer_and_print_template_program], and [string_of_env_error]);
   4. the conversion's fuel recursion at an empty fuel answers [ConvNotEnoughFuel "isconv_full"]
      ([isconv_full_fuel FuelO], for any arguments).
   The default fuel is checked to be non-empty ([PCUICFuelEta.default_fuel_step]). The machine runs inside a
   section on an abstract environment and an abstract well-typedness proof: it never reads them on this
   term (no constant, no variable), so the computation does not depend on them. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICPosition PCUICNormal PCUICSN.
From MetaRocq.SafeChecker Require Import PCUICFuelEta PCUICErrorsEta PCUICWfEnvEta PCUICWfReductionEta
  PCUICSafeReduceEta.
From MetaRocq.SafeChecker Require PCUICTypeCheckerEta PCUICSafeConversionEtaK4 PCUICSafeConversionEtaFacts
  PCUICSafeConversionEta.
From MetaRocq.SafeCheckerPlugin Require SafeTemplateCheckerEta.

Definition fuel_ind : inductive := {| inductive_mind := (MPfile ["EtaFuel"], "I"); inductive_ind := 0 |}.
Definition fuel_na : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition fuel_id : term := tLambda fuel_na (tInd fuel_ind []) (tRel 0).

(** [(fun x => x) ((fun x => x) I)]: the machine reaches [I] in five steps (two applications, two beta
    steps, the stop on [I]). *)
Definition five_steps : term := tApp fuel_id (tApp fuel_id (tInd fuel_ind [])).

Check PCUICFuelEta.default_fuel_step : match default_fuel with FuelS _ => True | FuelO => False end.

(** The expected message, printed by the plugin for a declaration refused for lack of fuel. *)
Definition fuel_message (site id : string) : string :=
  "Refused: the checker ran out of fuel in " ^ site ^
  " (a refusal for lack of fuel, not a type error), while checking " ^ id.

Section FuelTest.
  Context {cf : checker_flags} {wt : global_env_ext -> context -> term -> Prop} {wfP : global_env_ext -> Type}
    {EF : ReduceEnvFacts wt wfP} {TF : ReduceTypedFacts wt wfP}
    (X_type : abstract_env_impl) (X : X_type.π2.π1) {hX : AbstractEnvWf X_type X wfP}
    (h : forall Σ, abstract_env_ext_rel X Σ -> wt Σ [] (zip (five_steps, []))).

  (** 1. Fuel 1: out of fuel. *)
  Lemma eta_fuel_1_out :
    reduce_stack_fuel RedFlags.default X_type X [] (fuel_of_N 1) five_steps [] h = None.
  Proof. reflexivity. Qed.

  (** 1. Fuel 10: the weak-head normal form. *)
  Lemma eta_fuel_10_whnf :
    option_map (@proj1_sig _ _) (reduce_stack_fuel RedFlags.default X_type X [] (fuel_of_N 10) five_steps [] h)
    = Some (tInd fuel_ind [], []).
  Proof. reflexivity. Qed.

  (** 2.-3. The machine's [None] at fuel 1, as the checker reports it ([reduce_to_*] answer
      [NotEnoughFuel_comp] on [None]; [refuse_of_comp]; the [typing_result] the environment checker wraps
      in [IllFormedDecl]), printed by the plugin. *)
  Lemma eta_fuel_1_message :
    match PCUICTypeCheckerEta.check_result_forget
            (PCUICTypeCheckerEta.refuse_of_comp
               (match reduce_stack_fuel RedFlags.default X_type X [] (fuel_of_N 1) five_steps [] h with
                | None => NotEnoughFuel_comp "reduce_stack"
                | Some r => Checked_comp r
                end)) with
    | TypeError e =>
      SafeTemplateCheckerEta.print_env_error (empty_ext empty_global_env) (IllFormedDecl "five_steps" e)
    | Checked _ => "accepted"
    end = fuel_message "reduce_stack" "five_steps".
  Proof. reflexivity. Qed.
End FuelTest.

(** 2. The checker's mappings of the fuel outcome. *)
Example eta_fuel_refuse_of_comp :
  PCUICTypeCheckerEta.refuse_of_comp (@NotEnoughFuel_comp unit "reduce_to_sort")
  = PCUICTypeCheckerEta.Refused_c (NotEnoughFuel "reduce_to_sort").
Proof. reflexivity. Qed.

Example eta_fuel_check_of_comp :
  PCUICTypeCheckerEta.check_of_comp (@NotEnoughFuel_comp unit "check_codomain_ind")
  = PCUICTypeCheckerEta.Refused_c (NotEnoughFuel "check_codomain_ind").
Proof. reflexivity. Qed.

(** 2. The conversion's fuel outcome under another constructor is still found. *)
Example eta_fuel_nested_conv_error :
  conv_error_fuel
    (LambdaNotConvertibleTypes [] fuel_na (tInd fuel_ind []) (tRel 0) [] fuel_na (tInd fuel_ind []) (tRel 0)
       (ConvNotEnoughFuel "isconv_full"))
  = Some "isconv_full".
Proof. reflexivity. Qed.

Example eta_fuel_conv_error_other :
  conv_error_fuel (HeadMismatch Conv [] (tRel 0) [] (tRel 1)) = None.
Proof. reflexivity. Qed.

(** 3. The printers. *)
Example eta_fuel_plugin_message :
  SafeTemplateCheckerEta.print_env_error (empty_ext empty_global_env)
    (IllFormedDecl "c" (NotEnoughFuel "isconv_full"))
  = fuel_message "isconv_full" "c".
Proof. reflexivity. Qed.

Example eta_fuel_env_error_message :
  string_of_env_error (empty_ext empty_global_env) (IllFormedDecl "c" (NotEnoughFuel "arity_whnf"))
  = "Refused on c: the checker ran out of fuel in arity_whnf (a refusal for lack of fuel, not a type error)".
Proof. reflexivity. Qed.

Example eta_fuel_type_error_message :
  string_of_type_error (empty_ext empty_global_env) (NotEnoughFuel "reduce_stack")
  = "Refused: the checker ran out of fuel in reduce_stack (a refusal for lack of fuel, not a type error)".
Proof. reflexivity. Qed.

Example eta_fuel_conv_message :
  string_of_conv_error (empty_ext empty_global_env) (ConvNotEnoughFuel "isconv_full")
  = "The eta-conversion checker ran out of fuel in isconv_full (a refusal for lack of fuel, not a conversion failure).".
Proof. reflexivity. Qed.

(** 4. The conversion at an empty fuel: the out-of-fuel answer, for any arguments. *)
Section ConvFuel.
  Context {cf : checker_flags} {nor : normalizing_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
    {reduce_factsE : PCUICSafeReduceEta.ReduceTypedFactsE}
    {conv_factsE : PCUICSafeConversionEtaFacts.ConvTypedFactsE}.

  Lemma eta_fuel_conv_out cc wc Γ t1 π1 f1 h1 t2 π2 f2 h2 leq hx hv1 hv2 hwf1 hwf2 :
    match PCUICSafeConversionEta.isconv_full_fuel X_type X cc wc FuelO PCUICSafeConversionEtaK4.Reduction
            Γ t1 π1 f1 h1 t2 π2 f2 h2 leq hx hv1 hv2 hwf1 hwf2 I I I with
    | PCUICSafeConversionEta.Error e => conv_error_fuel e
    | PCUICSafeConversionEta.Success _ => None
    end = Some "isconv_full".
  Proof. reflexivity. Qed.
End ConvFuel.

Print Assumptions eta_fuel_1_out.
Print Assumptions eta_fuel_1_message.
