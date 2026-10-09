theory Ax_CyPhyCircus
  imports 
    "CyPhyCircus_Toolkit.CyPhyCircus_Toolkit"
begin

unbundle UTP_Syntax
unbundle Circus_Syntax

(* References: UCS = A. W. Roscoe, Understanding Concurrent Systems (Springer, 2010);
   TPC = A. W. Roscoe, The Theory and Practice of Concurrency (Prentice Hall, 1998);
   Oliveira = Formal Derivation of State-Rich Reactive Programs using Circus, extended York thesis (2005);
   Wei = Operational Semantics for Circus Time (2013);
   UTP = C. A. R. Hoare and He Jifeng, Unifying Theories of Programming (Prentice Hall, 1998);
   HOL-CSP = AFP HOL-CSP/HOL-CSPM; additional references: RC_HOL-CSP,
   https://github.com/laila-fangyan/RoboChart-Deadlock-HOLCSP-AG.
   Law identifiers follow RoboSAPIENS D1.4, Table "Implemented Circus step laws";
   (derived) marks the laws that table lists as derived. *)

section \<open> Types and Constants \<close>

typedecl ('e, 's) cyphyaction

type_synonym 'e cyphyprocess = "('e, unit) cyphyaction"

axiomatization where
  action_complete_lattice: "OFCLASS(('e, 's) cyphyaction, complete_lattice_class)"

instantiation cyphyaction :: (type, type) complete_lattice
begin
instance by (fact action_complete_lattice)
end

(* OR-01 - Refinement order: P \<sqsubseteq> Q iff Q \<le> P, so internal choice is the lattice join. *)
instantiation cyphyaction :: (type, type) refine
begin
definition "ref_by_cyphyaction = ((\<ge>) :: ('a, 'b) cyphyaction \<Rightarrow> ('a, 'b) cyphyaction \<Rightarrow> bool)"
definition "sref_by_cyphyaction = ((>) :: ('a, 'b) cyphyaction \<Rightarrow> ('a, 'b) cyphyaction \<Rightarrow> bool)"
instance 
  by (intro_classes, unfold_locales)
     (simp_all add: ref_by_cyphyaction_def sref_by_cyphyaction_def dual_order.strict_iff_not)
end

section \<open> IsaCyPhyCircus Operators \<close>

axiomatization
  cSpec          :: "('a \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) cyphyaction" and
  cAssigns       :: "('s \<Rightarrow> 's) \<Rightarrow> ('e, 's) cyphyaction" and
  cSeq           :: "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cCond          :: "('e, 's) cyphyaction \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cAlternList    :: "(('s \<Rightarrow> bool) \<times> ('e, 's) cyphyaction) list \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cVarBlock      :: "String.literal \<Rightarrow> 'a itself \<Rightarrow> (('a \<Longrightarrow> 's) \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> ('e, 's) cyphyaction" and
  cStop          :: "('e, 's) cyphyaction" and
  cChaos         :: "('e, 's) cyphyaction" and
  cGuard         :: "(bool, 's) expr \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cAssume        :: "(bool, 's) expr \<Rightarrow> ('e, 's) cyphyaction" and
  cInputPrefix   :: "('a, 'e) channel \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> (('s \<Rightarrow> bool) \<times> ('e, 's) cyphyaction)) \<Rightarrow> ('e, 's) cyphyaction" and
  cOutputPrefix  :: "('a, 'e) channel \<Rightarrow> ('a, 's) expr \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cSyncPrefix    :: "(unit, 'e) channel \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cEventPrefix   :: "'e \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cExtChoice     :: "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cExtChoiceIdx  :: "'i set \<Rightarrow> ('i \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> ('e, 's) cyphyaction" and
  cRename        :: "('e \<leftrightarrow> 'f) \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cHide          :: "('e, 's) cyphyaction \<Rightarrow> 'e set \<Rightarrow> ('e, 's) cyphyaction" and
  cParallelAct   :: "('a \<Longrightarrow> 's) \<Rightarrow> ('b \<Longrightarrow> 's) \<Rightarrow> 'e set \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cParallel      :: "'e set \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cInterrupt     :: "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction"

axiomatization
  cEvolve        :: "('a::real_normed_vector \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) cyphyaction" and
  cInterruptCond :: "('e, 's) cyphyaction \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) cyphyaction" and
  cTimeout       :: "('e, 's) cyphyaction \<Rightarrow> ('s \<Rightarrow> real) \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction"

definition cSkip :: "('e, 's) cyphyaction" where
"cSkip = cAssigns id"

adhoc_overloading 
  useq \<rightleftharpoons> cSeq and
  uassigns \<rightleftharpoons> cAssigns and
  ucond \<rightleftharpoons> cCond and
  ualtern_list \<rightleftharpoons> "cAlternList" and
  uvarblock \<rightleftharpoons> cVarBlock and
  Skip \<rightleftharpoons> cSkip and
  Stop \<rightleftharpoons> cStop and
  Guard \<rightleftharpoons> cGuard and
  ExtChoice \<rightleftharpoons> cExtChoice and 
  InputPrefix \<rightleftharpoons> cInputPrefix and
  OutputPrefix \<rightleftharpoons> cOutputPrefix and
  SyncPrefix \<rightleftharpoons> cSyncPrefix and
  Interrupt \<rightleftharpoons> cInterrupt and
  Rename \<rightleftharpoons> cRename and
  Hide \<rightleftharpoons> cHide and
  Parallel \<rightleftharpoons> cParallel and
  ParallelAct \<rightleftharpoons> cParallelAct and
  Evolve \<rightleftharpoons> cEvolve and
  Timeout \<rightleftharpoons> cTimeout and
  InterruptCond \<rightleftharpoons> cInterruptCond

section \<open> Axioms \<close>

subsection \<open>Monotonicity\<close>

(* MO-01 - Sequence, external choice and the three prefixes are monotonic in their action arguments. *)
axiomatization where
  cSeq_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> cSeq P\<^sub>1 Q\<^sub>1 \<le> cSeq P\<^sub>2 Q\<^sub>2" and
  cExtChoice_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> cExtChoice P\<^sub>1 Q\<^sub>1 \<le> cExtChoice P\<^sub>2 Q\<^sub>2" and
  cSync_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2 \<rbrakk> \<Longrightarrow> a \<rightarrow> P\<^sub>1 \<le> a \<rightarrow> P\<^sub>2" and
  cInput_mono [mono_rule]: "\<lbrakk> \<And> x::'a. P x \<le> Q x \<rbrakk> \<Longrightarrow> c\<^bold>?x \<rightarrow> P x \<le> c\<^bold>?x \<rightarrow> Q x" and
  cOutput_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2 \<rbrakk> \<Longrightarrow> c\<^bold>!e \<rightarrow> P\<^sub>1 \<le> c\<^bold>!e \<rightarrow> P\<^sub>2"
for P\<^sub>1 P\<^sub>2 Q\<^sub>1 Q\<^sub>2 :: "('e, 's) cyphyaction"
and P Q :: "'a \<Rightarrow> ('e, 's) cyphyaction"

subsection \<open> CSP Step Laws \<close>

named_theorems ax_step_laws
  \<open>axiomatic CyPhyCircus step laws\<close>

named_theorems ax_executable_step_laws
  \<open>CSP step laws oriented towards executable CyPhyCircus prefixes\<close>

(* Synchronisation prefix as an event prefix on the simple event evsimple. *)
axiomatization where
  ax_cSync_event_prefix [ax_step_laws]:
    "cSyncPrefix c P = cEventPrefix (evsimple c) P" and
  (* Output prefix with a state-independent value as an event prefix on the built event. *)
  ax_cOutput_event_prefix [ax_step_laws]:
    "cOutputPrefix d (\<lambda> s. v) Q = cEventPrefix (build\<^bsub>d\<^esub> v) Q"

(* SQ-01 to SQ-05 - Sequence: UCS pp. 132-133, (7.1)-(7.4); STOP as left zero, p. 132 (unnumbered) *)
axiomatization where
  (* SQ-01 - UCS p. 133, (7.4) *)
  ax_cSeq_event_prefix [ax_step_laws]:
    "cSeq (cEventPrefix e P) Q = cEventPrefix e (cSeq P Q)" and
  (* SQ-02 - UCS p. 132, (7.2) *)
  ax_cSeq_skip_left [ax_step_laws]:
    "cSeq cSkip P = P" and
  (* SQ-03 - UCS p. 132, (7.1) *)
  ax_cSeq_skip_right [ax_step_laws]:
    "cSeq P cSkip = P" and
  (* SQ-04 - UCS p. 132, STOP left-zero law (unnumbered) *)
  ax_cSeq_stop_left [ax_step_laws]:
    "cSeq cStop P = cStop" and
  (* SQ-05 - UCS p. 132, (7.3) *)
  ax_cSeq_assoc [ax_step_laws]:
    "cSeq (cSeq P Q) R = cSeq P (cSeq Q R)"

(* EC-01 to EC-04 - External choice: UCS p. 27, (2.16); p. 24, (2.1), (2.5), (2.3) *)
axiomatization where
  (* EC-01 - UCS p. 27, (2.16) *)
  ax_cExtChoice_stop_left [ax_step_laws]:
    "cExtChoice cStop P = P" and
  (* EC-02 - UCS p. 24, (2.1) *)
  ax_cExtChoice_idem [ax_step_laws]:
    "cExtChoice P P = P" and
  (* EC-03 - UCS p. 24, (2.5) *)
  ax_cExtChoice_assoc [ax_step_laws]:
    "cExtChoice (cExtChoice P Q) R = cExtChoice P (cExtChoice Q R)" and
  (* EC-04 - UCS p. 24, (2.3) *)
  ax_cExtChoice_comm:
    "cExtChoice P Q = cExtChoice Q P"

(* EC-01 / EC-04 - UCS p. 27, (2.16); p. 24, (2.3); STOP as right unit *)
lemma ax_cExtChoice_stop_right [ax_step_laws]:
  "cExtChoice P cStop = P"
  by (metis ax_cExtChoice_comm ax_cExtChoice_stop_left)

(* SQ-01 - UCS p. 133, (7.4); synchronisation-prefix form, via ax_cSync_event_prefix *)
lemma ax_cSeq_sync_prefix:
  "cSeq (cSyncPrefix c P) Q = cSyncPrefix c (cSeq P Q)"
  by (simp only: ax_cSync_event_prefix ax_cSeq_event_prefix)

lemmas [ax_executable_step_laws] =
  ax_cSeq_sync_prefix
  ax_cSeq_skip_left
  ax_cSeq_skip_right
  ax_cSeq_stop_left
  ax_cSeq_assoc
  ax_cExtChoice_stop_left
  ax_cExtChoice_stop_right
  ax_cExtChoice_idem
  ax_cExtChoice_assoc

subsection \<open>CyPhyCircus step and refinement laws\<close>

named_theorems cyphy_normalisation
  \<open>oriented controller equations; no automatic recursive unfolding\<close>
named_theorems cyphy_refinement
  \<open>conditional compositional refinement rules\<close>

definition cMprefix :: "'e set \<Rightarrow> ('e \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> ('e, 's) cyphyaction" where
  "cMprefix A K = cExtChoiceIdx A (\<lambda>e. cEventPrefix e (K e))"

definition cGlobalNdet :: "'i set \<Rightarrow> ('i \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> ('e, 's) cyphyaction" where
  "cGlobalNdet I P = (if I = {} then cStop else Sup (P ` I))"

definition cBoolGuard :: "bool \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" where
  "cBoolGuard b P = (if b then P else cStop)"

definition cSliding :: "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" where
  "cSliding P Q = sup (cExtChoice P Q) Q"

(* MP-01 - UCS p. 27, (2.15) *)
axiomatization where
  ax_mp_empty: "cExtChoiceIdx {} P = (cStop :: 'e cyphyprocess)"

(* MP-05 - UCS p. 27, (2.14); TPC p. 32, (1.14) *)
axiomatization where
  ax_mp_choice: "cExtChoice (cMprefix A P) (cMprefix B Q) =
    cMprefix (A \<union> B) (\<lambda>e. if e \<in> A \<inter> B then sup (P e) (Q e)
      else if e \<in> A then P e else Q e :: 'e cyphyprocess)"

(* MP-06 - UCS p. 27, (2.14) *)
axiomatization where
  ax_mp_indexed: "cExtChoiceIdx I (\<lambda>i. cMprefix (A i) (P i)) =
    cMprefix (\<Union>i\<in>I. A i)
      (\<lambda>e. cGlobalNdet {i \<in> I. e \<in> A i} (\<lambda>i. P i e :: 'e cyphyprocess))"

(* MP-07 - UCS p. 133, (7.4) *)
axiomatization where
  ax_mp_seq: "cSeq (cMprefix A P) Q =
    cMprefix A (\<lambda>e. cSeq (P e) (Q :: 'e cyphyprocess))"

(* CO-02 - UCS p. 133, (7.4) *)
axiomatization where
  ax_input_seq:
    "cSeq (cInputPrefix c A (\<lambda>x. (b x, P x))) Q =
      cInputPrefix c A (\<lambda>x. (b x, cSeq (P x) (Q :: ('e, 's) cyphyaction)))"

(* CO-03 - UCS p. 133, (7.4) *)
axiomatization where
  ax_output_seq:
    "cSeq (cOutputPrefix c v P) Q =
      cOutputPrefix c v (cSeq P (Q :: ('e, 's) cyphyaction))"

(* CO-04 - Oliveira p. 199, C.67, C.68 *)
axiomatization where
  ax_guard_constant [cyphy_normalisation]:
    "cGuard (\<lambda>_. b) P = cBoolGuard b (P :: ('e, 's) cyphyaction)"

(* HI-01 - UCS p. 96, (5.6), disjoint case; TPC p. 81, (3.6) *)
axiomatization where
  ax_hide_mprefix_disjoint:
    "A \<inter> S = {} \<Longrightarrow> cHide (cMprefix A P) S =
      cMprefix A (\<lambda>e. cHide (P e :: 'e cyphyprocess) S)"

(* HI-02 - UCS p. 96, (5.6), shared case; TPC p. 81, (3.6) *)
axiomatization where
  ax_hide_mprefix_shared:
    "A \<inter> S \<noteq> {} \<Longrightarrow> cHide (cMprefix A P) S =
      cSliding (cMprefix (A - S) (\<lambda>e. cHide (P e) S))
        (cGlobalNdet (A \<inter> S) (\<lambda>e. cHide (P e :: 'e cyphyprocess) S))"

(* HI-03 - Oliveira p. 209, C.120; AFP HOL-CSP Hiding_SKIP *)
axiomatization where
  ax_hide_skip [cyphy_normalisation]: "cHide cSkip S = (cSkip :: 'e cyphyprocess)"

(* HI-05 - UCS p. 95, (5.4) *)
axiomatization where
  ax_hide_empty [cyphy_normalisation]: "cHide P {} = (P :: 'e cyphyprocess)"

(* HI-06 - UCS p. 95, (5.3) *)
axiomatization where
  ax_hide_twice [cyphy_normalisation]:
    "finite A \<Longrightarrow>
      cHide (cHide P A) B = cHide (P :: 'e cyphyprocess) (A \<union> B)"

(* IN-01 - UCS p. 139, (7.5) *)
axiomatization where
  ax_interrupt_mprefix:
    "cInterrupt (cMprefix A P) Q =
      cExtChoice Q (cMprefix A (\<lambda>e. cInterrupt (P e) (Q :: 'e cyphyprocess)))"

(* RF-06 - Oliveira p. 71, Section 4.1 *)
axiomatization where
  ax_parallelAct_unit_mono [mono_rule, cyphy_refinement]:
    "P' \<le> P \<Longrightarrow> Q' \<le> Q \<Longrightarrow>
      cParallelAct 0\<^sub>L 0\<^sub>L A P' Q' \<le>
      cParallelAct 0\<^sub>L 0\<^sub>L A P (Q :: 'e cyphyprocess)"

(* RF-07 - TPC pp. 187-188, Theorem 8.2.1 *)
axiomatization where
  ax_rename_relation_mono:
    "Domain (R :: ('e \<times> 'e) set) = UNIV \<Longrightarrow> P' \<le> P \<Longrightarrow>
      cRename R P' \<le> cRename R (P :: 'e cyphyprocess)"

(* MO-03 - UCS p. 233, Theorem 10.1; AFP HOL-CSPM mono_GlobalDet_FD *)
axiomatization where
  cExtChoiceIdx_mono [mono_rule]:
    "(\<And>i. i \<in> A \<Longrightarrow> P i \<le> Q i) \<Longrightarrow>
      cExtChoiceIdx A P \<le> cExtChoiceIdx A Q"

(* MP-02 - UCS p. 20, indexed external choice; AFP HOL-CSPM GlobalDet_unit; opaque unit-state adaptation. *)
axiomatization where
  ax_mp_singleton: "cExtChoiceIdx {i} P = (P i :: 'e cyphyprocess)"

(* MP-03 - UCS p. 20, indexed external choice; AFP HOL-CSPM GlobalDet_factorization_union, reversed; opaque unit-state adaptation. *)
axiomatization where
  ax_mp_union: "cExtChoiceIdx (A \<union> B) P =
    cExtChoice (cExtChoiceIdx A P) (cExtChoiceIdx B P :: 'e cyphyprocess)"

(* MP-04 - UCS p. 20, indexed external choice; AFP HOL-CSPM GlobalDet_id, nonempty domain; opaque unit-state adaptation. *)
axiomatization where
  ax_mp_constant: "A \<noteq> {} \<Longrightarrow> cExtChoiceIdx A (\<lambda>_. P) = (P :: 'e cyphyprocess)"

(* CO-01 - UCS p. 7, input as prefix choice; AFP HOL-CSPM read_is_GlobalDet_write *)
axiomatization where
  ax_input_mprefix:
    "inj_on (prism_build c) A \<Longrightarrow>
      cInputPrefix c A (\<lambda>x. (\<lambda>_. b x, P x)) =
      cExtChoiceIdx {x \<in> A. b x}
        (\<lambda>x. cEventPrefix (prism_build c x) (P x :: 'e cyphyprocess))"

(* RF-02 - UCS p. 233, Theorem 10.1; AFP HOL-CSP mono_Hiding_FD; unit-state contract in the dual refinement order. *)
axiomatization where
  ax_hide_mono:
    "P' \<le> P \<Longrightarrow> cHide P' A \<le> cHide (P :: 'e cyphyprocess) A"

(* RF-04 - UCS p. 233, Theorem 10.1; AFP HOL-CSPM mono_Interrupt_FD; unit-state contract in the dual refinement order. *)
axiomatization where
  ax_interrupt_mono:
    "P' \<le> P \<Longrightarrow> Q' \<le> Q \<Longrightarrow>
      cInterrupt P' Q' \<le> cInterrupt P (Q :: 'e cyphyprocess)"

(* GC-01 - UCS p. 14, guard as conditional; RC_HOL-CSP GlobalDet_Guard; opaque fixed-Boolean adaptation. *)
axiomatization where
  ax_guard_indexed [cyphy_normalisation]:
    "cExtChoiceIdx I (\<lambda>i. cBoolGuard (b i) (P i)) =
      cExtChoiceIdx {i \<in> I. b i} (P :: 'i \<Rightarrow> 'e cyphyprocess)"

section \<open>Derived laws and further axioms\<close>

(* Selector equation of the Prisms record. *)
lemma refinement_prism_build:
  "prism_build (prism_ext match0 build0 more0) = build0"
  by (simp)

(* MO-02 (derived) - UCS p. 233, Theorem 10.1; from MO-01 (cSync_mono) and ax_cSync_event_prefix; AFP HOL-CSP mono_write0_FD *)
lemma cEventPrefix_mono [mono_rule]:
  assumes "R\<^sub>1 \<le> R\<^sub>2"
  shows "cEventPrefix e R\<^sub>1 \<le> cEventPrefix e R\<^sub>2"
proof -
  let ?c = "prism_ext (\<lambda>_. None) (\<lambda>_::unit. e) ()"
  have event: "evsimple ?c = e"
    by (simp add: evsimple_def refinement_prism_build)
  have "cSyncPrefix ?c R\<^sub>1 \<le> cSyncPrefix ?c R\<^sub>2"
    by (rule cSync_mono[OF assms])
  then show ?thesis
    by (simp only: ax_cSync_event_prefix event)
qed

definition cCompleteRenaming :: "('e \<times> 'e) set \<Rightarrow> ('e \<times> 'e) set" where
  "cCompleteRenaming R = R \<union> {(e,e) |e. e \<notin> Domain R}"

(* MP-01 - UCS p. 27, (2.15) *)
lemma cMprefix_empty [cyphy_normalisation]:
  "cMprefix {} P = (cStop :: 'e cyphyprocess)"
  by (simp only: cMprefix_def ax_mp_empty)

(* HI-04 (derived) - UCS p. 96, (5.6); p. 27, (2.15); from HI-01 and MP-01 *)
lemma ax_hide_stop [cyphy_normalisation]:
  "cHide cStop S = (cStop :: 'e cyphyprocess)"
  using ax_hide_mprefix_disjoint[of "{}" S "\<lambda>_. cStop"]
  by (simp add: cMprefix_empty)

(* MP-02 - from cMprefix_def and ax_mp_singleton; AFP GlobalDet_unit counterpart. *)
lemma cMprefix_singleton [cyphy_normalisation]:
  "cMprefix {e} P = cEventPrefix e (P e :: 'e cyphyprocess)"
  by (simp only: cMprefix_def ax_mp_singleton)

(* Proved from cGlobalNdet_def and the complete lattice. *)
lemma cGlobalNdet_empty [cyphy_normalisation]: "cGlobalNdet {} P = cStop"
  by (simp add: cGlobalNdet_def)

(* Proved from cGlobalNdet_def and the complete lattice. *)
lemma cGlobalNdet_singleton [cyphy_normalisation]: "cGlobalNdet {i} P = P i"
  by (simp add: cGlobalNdet_def)

(* CO-04 - Oliveira p. 199, C.67; Boolean guard *)
lemma cBoolGuard_true [cyphy_normalisation]: "cBoolGuard True P = P"
  (* Boolean guard - Oliveira p. 199, C.68 *)
  and cBoolGuard_false [cyphy_normalisation]: "cBoolGuard False P = cStop"
  (* Boolean guard - Oliveira p. 199, C.69 *)
  and cBoolGuard_stop [cyphy_normalisation]: "cBoolGuard b cStop = cStop"
  (* ST-03 - Oliveira p. 198, C.57 *)
  and cBoolGuard_conj [cyphy_normalisation]:
    "cBoolGuard b (cBoolGuard c P) = cBoolGuard (b \<and> c) P"
  by (simp_all add: cBoolGuard_def)

(* MP-01 - UCS p. 27, (2.15) *)
lemma cBoolGuard_mprefix [cyphy_normalisation]:
  "cBoolGuard b (cMprefix A P) = cMprefix {e \<in> A. b} (P :: 'e \<Rightarrow> 'e cyphyprocess)"
  by (cases b; simp add: cBoolGuard_def cMprefix_empty)

(* Proved from cCompleteRenaming_def by set algebra. *)
lemma cCompleteRenaming_total:
  "Domain (cCompleteRenaming R) = UNIV"
  by (auto simp: cCompleteRenaming_def Domain_def)

(* RF-07 - TPC pp. 187-188, Theorem 8.2.1 *)
lemma cRename_complete_mono [mono_rule, cyphy_refinement]:
  "P' \<le> P \<Longrightarrow>
    cRename (cCompleteRenaming R) P' \<le>
    cRename (cCompleteRenaming R) (P :: 'e cyphyprocess)"
  by (rule ax_rename_relation_mono[OF cCompleteRenaming_total])

(* MP-02 / MP-03 - from ax_mp_singleton and ax_mp_union. *)
lemma cExtChoice_as_indexed:
  "cExtChoice P Q = cExtChoiceIdx {False, True}
    (\<lambda>i. if i then Q else P :: 'e cyphyprocess)"
proof -
  have "cExtChoiceIdx ({False} \<union> {True}) (\<lambda>i. if i then Q else P) = cExtChoice P Q"
    by (simp only: ax_mp_union ax_mp_singleton if_False if_True)
  then show ?thesis by (metis insert_is_Un)
qed

(* GC-01 / MP-02 / MP-03 - from ax_guard_indexed and cExtChoice_as_indexed; RC counterpart Guard_Det_Guard_to_GlobalDet. *)
lemma cGuardedChoice_as_indexed:
  "cExtChoice (cBoolGuard b P) (cBoolGuard c Q) =
    cExtChoiceIdx {i \<in> {False, True}. if i then c else b}
      (\<lambda>i. if i then Q else P :: 'e cyphyprocess)"
proof -
  have E: "(\<lambda>i. if i then cBoolGuard c Q else cBoolGuard b P) =
    (\<lambda>i. cBoolGuard (if i then c else b) (if i then Q else P))"
    by (rule ext, rename_tac i, case_tac i, simp_all)
  show ?thesis
    by (simp only: cExtChoice_as_indexed E ax_guard_indexed)
qed

(* Proved from cExtChoiceIdx_mono and cEventPrefix_mono. *)
lemma cMprefix_mono [cyphy_refinement]:
  "(\<And>e. e \<in> A \<Longrightarrow> P e \<le> Q e) \<Longrightarrow> cMprefix A P \<le> cMprefix A Q"
  unfolding cMprefix_def by (intro cExtChoiceIdx_mono cEventPrefix_mono)

(* Proved from cBoolGuard_def. *)
lemma cBoolGuard_mono [cyphy_refinement]: "P \<le> Q \<Longrightarrow> cBoolGuard b P \<le> cBoolGuard b Q"
  by (simp add: cBoolGuard_def)

(* CO-04 - unit-state instance of ax_guard_constant. *)
lemma cGuard_unit_bool:
  fixes b :: "unit \<Rightarrow> bool" and P :: "'e cyphyprocess"
  shows "cGuard b P = cBoolGuard (b ()) P"
proof -
  have fixed: "b = (\<lambda>_::unit. b ())" by (simp add: fun_eq_iff)
  show ?thesis
    using arg_cong[OF fixed, of "\<lambda>g. cGuard g P"]
    by (simp only: ax_guard_constant)
qed

(* CO-04 - from cGuard_unit_bool and cBoolGuard_mono. *)
lemma cGuard_unit_mono [mono_rule, cyphy_refinement]:
  fixes b :: "unit \<Rightarrow> bool" and P Q :: "'e cyphyprocess"
  shows "P \<le> Q \<Longrightarrow> cGuard b P \<le> cGuard b Q"
  by (simp only: cGuard_unit_bool; rule cBoolGuard_mono)

(* EC-02 - UCS p. 24, (2.1) *)
lemma cExtChoice_same_bound [cyphy_refinement]:
  "P \<le> X \<Longrightarrow> Q \<le> X \<Longrightarrow> cExtChoice P Q \<le> X"
  by (metis ax_cExtChoice_idem cExtChoice_mono)

(* MP-04 - from ax_mp_constant and cExtChoiceIdx_mono; RC counterpart mono_GlobalDet_FD_const. *)
lemma cExtChoiceIdx_bound [cyphy_refinement]:
  "I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> P i \<le> X) \<Longrightarrow>
    cExtChoiceIdx I P \<le> (X :: 'e cyphyprocess)"
  by (metis ax_mp_constant cExtChoiceIdx_mono)

(* GC-01 / MP-04 - from ax_guard_indexed and cExtChoiceIdx_bound; RC counterpart mono_GlobalDet_Guard_FD_const. *)
lemma cExtChoiceIdx_guard_bound [cyphy_refinement]:
  "(\<exists>i\<in>I. b i) \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> b i \<Longrightarrow> P i \<le> X) \<Longrightarrow>
    cExtChoiceIdx I (\<lambda>i. cBoolGuard (b i) (P i)) \<le> (X :: 'e cyphyprocess)"
  by (simp only: ax_guard_indexed; rule cExtChoiceIdx_bound; auto)

(* Proved from Isabelle/HOL SUP_mono and cGlobalNdet_def. *)
lemma cGlobalNdet_mono [cyphy_refinement]:
  "(\<And>i. i \<in> I \<Longrightarrow> P i \<le> Q i) \<Longrightarrow> cGlobalNdet I P \<le> cGlobalNdet I Q"
  unfolding cGlobalNdet_def by (auto intro: SUP_mono)

(* Proved from Isabelle/HOL lfp_mono on the function space. *)
lemma cyphy_joint_lfp_mono [cyphy_refinement]:
  "(\<And>X i. F X i \<le> G X i) \<Longrightarrow>
    lfp F i \<le> lfp G i"
  by (rule le_funD, rule lfp_mono, rule le_funI; assumption)

(* CO-01 - from ax_input_mprefix with indexed-choice and prefix monotonicity; AFP read_is_GlobalDet_write counterpart. *)
lemma cInputPrefix_unit_mono [mono_rule, cyphy_refinement]:
  fixes b :: "'a \<Rightarrow> unit \<Rightarrow> bool"
    and P Q :: "'a \<Rightarrow> 'e cyphyprocess"
  assumes injective: "inj_on (prism_build c) A"
    and ordered: "\<And>x. x \<in> A \<Longrightarrow> P x \<le> Q x"
  shows "cInputPrefix c A (\<lambda>x. (b x, P x)) \<le>
    cInputPrefix c A (\<lambda>x. (b x, Q x))"
proof -
  have fixed: "b = (\<lambda>x (_::unit). b x ())"
    by (simp add: fun_eq_iff)
  have left: "cInputPrefix c A (\<lambda>x. (b x, P x)) =
      cInputPrefix c A (\<lambda>x. (\<lambda>_::unit. b x (), P x))"
    using arg_cong[OF fixed, of "\<lambda>g. cInputPrefix c A (\<lambda>x. (g x, P x))"]
    by simp
  have right: "cInputPrefix c A (\<lambda>x. (b x, Q x)) =
      cInputPrefix c A (\<lambda>x. (\<lambda>_::unit. b x (), Q x))"
    using arg_cong[OF fixed, of "\<lambda>g. cInputPrefix c A (\<lambda>x. (g x, Q x))"]
    by simp
  show ?thesis
    by (simp only: left right ax_input_mprefix[OF injective];
        intro cExtChoiceIdx_mono cEventPrefix_mono; auto intro: ordered)
qed

(* Proved from evsimple_def, chinst1_def and refinement_prism_build. *)
lemma evsimple_chinst1:
  "evsimple (chinst1 c v) = build\<^bsub>c\<^esub> v"
  by (simp only: evsimple_def chinst1_def refinement_prism_build)

(* Proved from ax_cSync_event_prefix and evsimple_chinst1. *)
lemma ax_cSync_chinst1_event_prefix:
  "cSyncPrefix (chinst1 c v) P = cEventPrefix (build\<^bsub>c\<^esub> v) P"
  by (simp only: ax_cSync_event_prefix evsimple_chinst1)

named_theorems cyphy_search_preparation
  \<open>equations preparing an algebraic residual for upstream search\<close>

(* GC-01 / MP-02 / MP-03 - cGuardedChoice_as_indexed, reversed. *)
lemma search_bool_filtered_choice [cyphy_search_preparation]:
  fixes P :: "bool \<Rightarrow> 'e cyphyprocess"
  shows "cExtChoiceIdx {i \<in> {False, True}. if i then c else b} P =
    cExtChoice (cBoolGuard b (P False)) (cBoolGuard c (P True))"
proof -
  have branches: "(\<lambda>i. if i then P True else P False) = P"
    by (rule ext, rename_tac i, case_tac i, simp_all)
  show ?thesis
    using cGuardedChoice_as_indexed[of b "P False" c "P True"]
    by (simp only: branches)
qed

(* CO-01 - identity-prism instance of ax_input_mprefix; AFP read_is_GlobalDet_write counterpart. *)
lemma search_mprefix_as_input [cyphy_search_preparation]:
  fixes P :: "'e \<Rightarrow> 'e cyphyprocess"
  shows "cMprefix A P =
    cInputPrefix prism_id A (\<lambda>e. (\<lambda>_. True, P e))"
proof -
  have injective: "inj_on (prism_build (prism_id :: ('e, 'e) channel)) A"
    by (simp add: prism_id_def refinement_prism_build)
  have input: "cInputPrefix prism_id A (\<lambda>e. (\<lambda>_. True, P e)) =
    cExtChoiceIdx {e \<in> A. True}
      (\<lambda>e. cEventPrefix (prism_build prism_id e) (P e))"
    by (rule ax_input_mprefix[OF injective])
  show ?thesis
    using input by (simp add: prism_id_def refinement_prism_build cMprefix_def)
qed

(* Proved from ax_cOutput_event_prefix and the identity-prism definitions. *)
lemma event_prefix_as_output [cyphy_search_preparation]:
  "cEventPrefix e P = cOutputPrefix prism_id (\<lambda>_. e) P"
  by (simp only: ax_cOutput_event_prefix prism_id_def refinement_prism_build id_apply)

(* MP-02 / MP-03 - from ax_mp_union and ax_mp_singleton. *)
lemma search_indexed_insert [cyphy_search_preparation]:
  "cExtChoiceIdx (insert i I) P =
    cExtChoice (P i) (cExtChoiceIdx I P :: 'e cyphyprocess)"
  using ax_mp_union[of "{i}" I P] by (simp add: ax_mp_singleton)

(* MP-02 / MP-03 - from cMprefix_def and search_indexed_insert. *)
lemma search_mprefix_insert [cyphy_search_preparation]:
  "cMprefix (insert e A) P =
    cExtChoice (cEventPrefix e (P e)) (cMprefix A P :: 'e cyphyprocess)"
  by (simp only: cMprefix_def search_indexed_insert)

lemmas [cyphy_refinement] = cSeq_mono cExtChoice_mono cEventPrefix_mono
  cSync_mono cInput_mono cOutput_mono cExtChoiceIdx_mono ax_hide_mono ax_interrupt_mono

lemmas [mono_rule] = cMprefix_mono cBoolGuard_mono cGlobalNdet_mono ax_hide_mono ax_interrupt_mono

lemmas [cyphy_normalisation] = ax_mp_empty ax_mp_singleton ax_mp_seq
  ax_input_seq ax_output_seq ax_input_mprefix ax_mp_choice ax_mp_indexed
  cGuardedChoice_as_indexed ax_hide_mprefix_disjoint ax_hide_mprefix_shared ax_interrupt_mprefix

lemmas [cyphy_search_preparation] = ax_mp_empty cMprefix_empty

declare [[literal_variables]]

(* notation useq (infixr ";" 55) *) \<comment> \<open>this conflicts with Isabelle's let syntax\<close> 

syntax "_useq_iter" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (";_/\<in>_. _" [0, 0, 10] 10)

end