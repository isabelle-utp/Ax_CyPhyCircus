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
   tick-tock-CSP = Isabelle mechanisation, https://github.com/UoY-RoboStar/tick-tock-CSP;
   core_timed.csp = RoboTool timed CSP library, robochart-csp-gen, lib/semantics/timed/core_timed.csp.
   FDR manual = https://cocotec.io/fdr/manual, CSPM;
   RoboChart reference manual = https://robostar.cs.york.ac.uk/publications/techreports/reports/robochart-reference.pdf.
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

(* Hoare triples -- ensures all reachable states of the action satisfy the spec *)
axiomatization
  cPrePost       :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"

adhoc_overloading hoare_rel \<rightleftharpoons> cPrePost

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

axiomatization
  cException       :: "('e, 's) cyphyaction \<Rightarrow> 'e set \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" and
  cPrioritise      :: "'e set \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction"

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

subsection \<open> Derived operators \<close>

(* Prefix choice *)
definition cPrefixChoice :: "'e set \<Rightarrow> ('e \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> ('e, 's) cyphyaction" where
  "cPrefixChoice A K = cExtChoiceIdx A (\<lambda>e. cEventPrefix e (K e))"

(* Indexed internal choice *)
definition cIntChoiceIdx :: "'i set \<Rightarrow> ('i \<Rightarrow> ('e, 's) cyphyaction) \<Rightarrow> ('e, 's) cyphyaction" where
  "cIntChoiceIdx I P = (if I = {} then cStop else Sup (P ` I))"

(* Boolean guard *)
definition cBoolGuard :: "bool \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" where
  "cBoolGuard b P = (if b then P else cStop)"

(* Sliding choice *)
definition cSlidingChoice :: "('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" where
  "cSlidingChoice P Q = sup (cExtChoice P Q) Q"

(* Renaming by a function *)
definition cRenameFun :: "('e \<Rightarrow> 'e) \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" where
  "cRenameFun f P = cRename {(x, f x) |x. True} P"

subsection \<open> Timed operators \<close>

(* The event tock *)
class tock =
  fixes cTock :: 'a

(* Timed Stop - FDR manual, Timed Sections: TSTOP = tock -> TSTOP *)
definition cTStop :: "('e::tock, 's) cyphyaction" where
  "cTStop = lfp (\<lambda>X. cEventPrefix cTock X)"

(* Timed Skip - FDR manual, Timed Sections: TSKIP = SKIP [] tock -> TSKIP *)
definition cTSkip :: "('e::tock, 's) cyphyaction" where
  "cTSkip = lfp (\<lambda>X. cExtChoice cSkip (cEventPrefix cTock X))"

(* Timed prefix - FDR manual, Timed Sections: X = tock -> X [] P, for P a prefix a -> Q or a choice of prefixes,
   written without tock; for a choice this is [+ {tock} +] with the tock factored out *)
definition cTPrefix :: "('e::tock, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" where
  "cTPrefix P = lfp (\<lambda>X. cExtChoice P (cEventPrefix cTock X))"

(* Timed parallel composition - FDR manual, Timed Sections: P [| union({tock},A) |] Q *)
definition cTParallelAct :: "('a \<Longrightarrow> 's) \<Rightarrow> ('b \<Longrightarrow> 's) \<Rightarrow> 'e::tock set \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" where
  "cTParallelAct ns\<^sub>1 ns\<^sub>2 A P Q = cParallelAct ns\<^sub>1 ns\<^sub>2 (insert cTock A) P Q"

definition cTParallel :: "'e::tock set \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" where
  "cTParallel A P Q = cParallel (insert cTock A) P Q"

(* Wait - RoboChart reference manual, Rules 94, 97, 98 and 100; FDR manual, WAIT *)
primrec cWait :: "nat \<Rightarrow> ('e::tock, 's) cyphyaction" where
  "cWait 0 = cTSkip" |
  "cWait (Suc d) = cEventPrefix cTock (cWait d)"

(* Timeout by one time unit - RoboChart reference manual, Appendix C.1.1; core_timed.csp, TimeOut_1; P is written
   without tock *)
definition cInitialTimeout1 :: "('e::tock, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" where
  "cInitialTimeout1 P Q = cExtChoice P (cEventPrefix cTock Q)"

(* Start deadline - core_timed.csp, StartBy, under maximal progress; P is written without tock *)
primrec cStartDeadline :: "nat \<Rightarrow> ('e::tock, 's) cyphyaction \<Rightarrow> ('e, 's) cyphyaction" where
  "cStartDeadline 0 P = P" |
  "cStartDeadline (Suc d) P = cExtChoice P (cEventPrefix cTock (cStartDeadline d P))"

(* Timed section - FDR manual, Timed Sections *)
bundle Timed_Section
begin

no_adhoc_overloading
  Skip \<rightleftharpoons> cSkip and
  Stop \<rightleftharpoons> cStop and
  Parallel \<rightleftharpoons> cParallel and
  ParallelAct \<rightleftharpoons> cParallelAct

adhoc_overloading
  Skip \<rightleftharpoons> cTSkip and
  Stop \<rightleftharpoons> cTStop and
  Parallel \<rightleftharpoons> cTParallel and
  ParallelAct \<rightleftharpoons> cTParallelAct

end

section \<open> Axioms \<close>

subsection \<open>Monotonicity\<close>

(* MO-01 - Sequence, external choice, the three prefixes, interrupt, hiding, parallel composition,
   renaming and guards are monotonic in their action arguments. *)
axiomatization where
  cSeq_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> cSeq P\<^sub>1 Q\<^sub>1 \<le> cSeq P\<^sub>2 Q\<^sub>2" and
  cExtChoice_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> cExtChoice P\<^sub>1 Q\<^sub>1 \<le> cExtChoice P\<^sub>2 Q\<^sub>2" and
  cSync_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2 \<rbrakk> \<Longrightarrow> a \<rightarrow> P\<^sub>1 \<le> a \<rightarrow> P\<^sub>2" and
  cInput_mono [mono_rule]: "\<lbrakk> \<And> x::'a. P x \<le> Q x \<rbrakk> \<Longrightarrow> c\<^bold>?x \<rightarrow> P x \<le> c\<^bold>?x \<rightarrow> Q x" and
  cOutput_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2 \<rbrakk> \<Longrightarrow> c\<^bold>!e \<rightarrow> P\<^sub>1 \<le> c\<^bold>!e \<rightarrow> P\<^sub>2" and
  cInterrupt_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> cInterrupt P\<^sub>1 Q\<^sub>1 \<le> cInterrupt P\<^sub>2 Q\<^sub>2" and
  cHide_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2 \<rbrakk> \<Longrightarrow> cHide P\<^sub>1 A \<le> cHide P\<^sub>2 A" and
  cParallelAct_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> cParallelAct ns\<^sub>1 ns\<^sub>2 cs P\<^sub>1 Q\<^sub>1 \<le> cParallelAct ns\<^sub>1 ns\<^sub>2 cs P\<^sub>2 Q\<^sub>2" and
  cRename_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2 \<rbrakk> \<Longrightarrow> cRename R P\<^sub>1 \<le> cRename R P\<^sub>2" and
  cGuard_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2 \<rbrakk> \<Longrightarrow> cGuard b P\<^sub>1 \<le> cGuard b P\<^sub>2"
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

(* MP-01 - UCS p. 27, (2.15) *)
axiomatization where
  ax_mp_empty: "cExtChoiceIdx {} P = (cStop :: 'e cyphyprocess)"

(* MP-05 - UCS p. 27, (2.14); TPC p. 32, (1.14) *)
axiomatization where
  ax_mp_choice: "cExtChoice (cPrefixChoice A P) (cPrefixChoice B Q) =
    cPrefixChoice (A \<union> B) (\<lambda>e. if e \<in> A \<inter> B then sup (P e) (Q e)
      else if e \<in> A then P e else Q e :: 'e cyphyprocess)"

(* MP-06 - UCS p. 27, (2.14) *)
axiomatization where
  ax_mp_indexed: "cExtChoiceIdx I (\<lambda>i. cPrefixChoice (A i) (P i)) =
    cPrefixChoice (\<Union>i\<in>I. A i)
      (\<lambda>e. cIntChoiceIdx {i \<in> I. e \<in> A i} (\<lambda>i. P i e :: 'e cyphyprocess))"

(* MP-07 - UCS p. 133, (7.4) *)
axiomatization where
  ax_mp_seq: "cSeq (cPrefixChoice A P) Q =
    cPrefixChoice A (\<lambda>e. cSeq (P e) (Q :: 'e cyphyprocess))"

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

(* SY-01 - UCS p. 60, (3.10) *)
axiomatization where
  ax_mprefix_parallel:
    "cParallel S (cPrefixChoice A P) (cPrefixChoice B Q) =
      cExtChoice
        (cPrefixChoice (A - S) (\<lambda>e. cParallel S (P e) (cPrefixChoice B Q)))
        (cExtChoice
          (cPrefixChoice (B - S) (\<lambda>e. cParallel S (cPrefixChoice A P) (Q e)))
          (cPrefixChoice (A \<inter> B \<inter> S)
            (\<lambda>e. cParallel S (P e) (Q e :: 'e cyphyprocess))))"

(* SY-02 - Oliveira p. 205, C.90; AFP HOL-CSP SKIP_Sync_SKIP *)
axiomatization where
  ax_parallel_skip [cyphy_normalisation]:
    "cParallel S cSkip cSkip = (cSkip :: 'e cyphyprocess)"

(* SY-03 - Oliveira p. 205, C.91; UCS p. 60, (3.10) *)
axiomatization where
  ax_parallel_stop [cyphy_normalisation]:
    "cParallel S cStop cStop = (cStop :: 'e cyphyprocess)"

(* HI-01 - UCS p. 96, (5.6), disjoint case; TPC p. 81, (3.6) *)
axiomatization where
  ax_hide_mprefix_disjoint:
    "A \<inter> S = {} \<Longrightarrow> cHide (cPrefixChoice A P) S =
      cPrefixChoice A (\<lambda>e. cHide (P e :: 'e cyphyprocess) S)"

(* HI-02 - UCS p. 96, (5.6), shared case; TPC p. 81, (3.6) *)
axiomatization where
  ax_hide_mprefix_shared:
    "A \<inter> S \<noteq> {} \<Longrightarrow> cHide (cPrefixChoice A P) S =
      cSlidingChoice (cPrefixChoice (A - S) (\<lambda>e. cHide (P e) S))
        (cIntChoiceIdx (A \<inter> S) (\<lambda>e. cHide (P e :: 'e cyphyprocess) S))"

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

(* RN-01 - UCS p. 106, (5.15) *)
axiomatization where
  ax_rename_mprefix:
    "cRenameFun f (cPrefixChoice A P) = cPrefixChoice (f ` A)
      (\<lambda>y. cIntChoiceIdx {x \<in> A. y = f x}
        (\<lambda>x. cRenameFun f (P x :: 'e cyphyprocess)))"

(* IN-01 - UCS p. 139, (7.5) *)
axiomatization where
  ax_interrupt_mprefix:
    "cInterrupt (cPrefixChoice A P) Q =
      cExtChoice Q (cPrefixChoice A (\<lambda>e. cInterrupt (P e) (Q :: 'e cyphyprocess)))"

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

(* ST-01 - UTP p. 50, L3; Isabelle/UTP assigns_comp *)
axiomatization where
  ax_assign_comp [cyphy_normalisation]:
    "cSeq (cAssigns f) (cAssigns g) = cAssigns (g \<circ> f)"

(* ST-02 - UTP p. 50, L4; Isabelle/UTP assign_rcond *)
axiomatization where
  ax_assign_cond [cyphy_normalisation]:
    "cSeq (cAssigns f) (cCond P b Q) =
      cCond (cSeq (cAssigns f) P) (b \<circ> f) (cSeq (cAssigns f) Q)"

(* ST-03 - Oliveira p. 198, C.57 *)
axiomatization where
  ax_guard_conj [cyphy_normalisation]:
    "cGuard b (cGuard c P) = cGuard (\<lambda>s. b s \<and> c s) P"

(* ALG-01 - UCS p. 25, (2.7) *)
axiomatization where
  ax_alg_ext_internal:
    "cExtChoice P (sup Q R) =
      sup (cExtChoice P Q) (cExtChoice P (R :: 'e cyphyprocess))"

(* ALG-02 - UCS p. 25, (2.9) *)
axiomatization where
  ax_alg_internal_prefix:
    "sup (cEventPrefix e P) (cEventPrefix e Q) =
      cEventPrefix e (sup P (Q :: 'e cyphyprocess))"

(* ALG-03 - UCS p. 95, (5.1); TPC p. 78, (3.1) *)
axiomatization where
  ax_alg_hide_internal:
    "cHide (sup P Q) S = sup (cHide P S) (cHide (Q :: 'e cyphyprocess) S)"

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

(* RF-01 - UCS p. 233, Theorem 10.1; AFP HOL-CSP mono_Sync_FD *)
axiomatization where
  ax_parallel_mono:
    "P' \<le> P \<Longrightarrow> Q' \<le> Q \<Longrightarrow>
      cParallel A P' Q' \<le> cParallel A P (Q :: 'e cyphyprocess)"

(* RF-02 - UCS p. 233, Theorem 10.1; AFP HOL-CSP mono_Hiding_FD; unit-state contract in the dual refinement order. *)
axiomatization where
  ax_hide_mono:
    "P' \<le> P \<Longrightarrow> cHide P' A \<le> cHide (P :: 'e cyphyprocess) A"

(* RF-03 - UCS p. 233, Theorem 10.1; AFP HOL-CSP mono_Renaming_FD *)
axiomatization where
  ax_rename_mono:
    "P' \<le> P \<Longrightarrow>
      cRename {(e, f e) |e. True} P' \<le>
      cRename {(e, f e) |e. True} (P :: 'e cyphyprocess)"

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

(* Differential induction, cut, and weakening *)
axiomatization where
  cEvolve_dInduct: "diff_inv_on a (\<lambda> _. f) G (Collect ((\<le>) 0))\<^sub>e UNIV 0 (I)\<^sub>e \<Longrightarrow> H{I} cEvolve a f G {I}" and
  cEvolve_dCut: "\<lbrakk> H{P} cEvolve a f (G)\<^sub>e {P}; H{Q} cEvolve a f (G \<and> P)\<^sub>e {Q} \<rbrakk> \<Longrightarrow> H{P \<and> Q} cEvolve a f (G)\<^sub>e {P \<and> Q}" and
  cEvolve_dWeaken: "\<lbrakk> `G \<longrightarrow> Q` \<rbrakk> \<Longrightarrow> H{P} cEvolve a f (G)\<^sub>e {Q}"
  for a :: "'a::real_normed_vector \<Longrightarrow> 's" and f :: "'s \<Rightarrow> 's"

method dInduct = ((simp only: SEXP_apply named_expr_defs)?; (rule_tac cEvolve_dInduct); 
    rule_tac lderiv_rules; 
    simp add: framed_derivs ldifferentiable closure usubst unrest_ssubst unrest usubst_eval)

method dCut = (rule cEvolve_dCut)

method dWeaken = (rule_tac cEvolve_dWeaken; expr_simp; auto simp add: field_simps)

method dInduct_mega uses facts = 
  ( fact facts \<comment> \<open> (1) Try any facts we have provided \<close>
  | (dWeaken ; force) \<comment> \<open> (2) Try differential weakening \<close>
  | dCut \<comment> \<open> (4) Try differential cut  \<close>
  | (dInduct) \<comment> \<open> (5) Try differential induction \<close>
  )+

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
lemma cPrefixChoice_empty [cyphy_normalisation]:
  "cPrefixChoice {} P = (cStop :: 'e cyphyprocess)"
  by (simp only: cPrefixChoice_def ax_mp_empty)

(* HI-04 (derived) - UCS p. 96, (5.6); p. 27, (2.15); from HI-01 and MP-01 *)
lemma ax_hide_stop [cyphy_normalisation]:
  "cHide cStop S = (cStop :: 'e cyphyprocess)"
  using ax_hide_mprefix_disjoint[of "{}" S "\<lambda>_. cStop"]
  by (simp add: cPrefixChoice_empty)

(* MP-02 - from cPrefixChoice_def and ax_mp_singleton; AFP GlobalDet_unit counterpart. *)
lemma cPrefixChoice_singleton [cyphy_normalisation]:
  "cPrefixChoice {e} P = cEventPrefix e (P e :: 'e cyphyprocess)"
  by (simp only: cPrefixChoice_def ax_mp_singleton)

(* Proved from cIntChoiceIdx_def and the complete lattice. *)
lemma cIntChoiceIdx_empty [cyphy_normalisation]: "cIntChoiceIdx {} P = cStop"
  by (simp add: cIntChoiceIdx_def)

(* Proved from cIntChoiceIdx_def and the complete lattice. *)
lemma cIntChoiceIdx_singleton [cyphy_normalisation]: "cIntChoiceIdx {i} P = P i"
  by (simp add: cIntChoiceIdx_def)

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
  "cBoolGuard b (cPrefixChoice A P) = cPrefixChoice {e \<in> A. b} (P :: 'e \<Rightarrow> 'e cyphyprocess)"
  by (cases b; simp add: cBoolGuard_def cPrefixChoice_empty)

(* RN-01 - UCS p. 106, (5.15) *)
lemma cRename_graph_mprefix [cyphy_normalisation]:
  fixes P :: "'e \<Rightarrow> 'e cyphyprocess"
  shows "cRename {(e, f e) |e. True} (cPrefixChoice A P) = cPrefixChoice (f ` A)
    (\<lambda>y. cIntChoiceIdx {x \<in> A. y = f x}
      (\<lambda>x. cRename {(e, f e) |e. True} (P x)))"
  by (rule ax_rename_mprefix[unfolded cRenameFun_def])

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

(* Proved from cExtChoiceIdx_mono and Isabelle/HOL antisym. *)
lemma cExtChoiceIdx_cong:
  "(\<And>i. i \<in> I \<Longrightarrow> P i = Q i) \<Longrightarrow>
    cExtChoiceIdx I P = cExtChoiceIdx I Q"
  by (rule antisym; rule cExtChoiceIdx_mono; simp)

(* Proved from cExtChoiceIdx_mono and cEventPrefix_mono. *)
lemma cPrefixChoice_mono [cyphy_refinement]:
  "(\<And>e. e \<in> A \<Longrightarrow> P e \<le> Q e) \<Longrightarrow> cPrefixChoice A P \<le> cPrefixChoice A Q"
  unfolding cPrefixChoice_def by (intro cExtChoiceIdx_mono cEventPrefix_mono)

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

(* Proved from Isabelle/HOL SUP_mono and cIntChoiceIdx_def. *)
lemma cIntChoiceIdx_mono [cyphy_refinement]:
  "(\<And>i. i \<in> I \<Longrightarrow> P i \<le> Q i) \<Longrightarrow> cIntChoiceIdx I P \<le> cIntChoiceIdx I Q"
  unfolding cIntChoiceIdx_def by (auto intro: SUP_mono)

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
  shows "cPrefixChoice A P =
    cInputPrefix prism_id A (\<lambda>e. (\<lambda>_. True, P e))"
proof -
  have injective: "inj_on (prism_build (prism_id :: ('e, 'e) channel)) A"
    by (simp add: prism_id_def refinement_prism_build)
  have input: "cInputPrefix prism_id A (\<lambda>e. (\<lambda>_. True, P e)) =
    cExtChoiceIdx {e \<in> A. True}
      (\<lambda>e. cEventPrefix (prism_build prism_id e) (P e))"
    by (rule ax_input_mprefix[OF injective])
  show ?thesis
    using input by (simp add: prism_id_def refinement_prism_build cPrefixChoice_def)
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

(* MP-02 / MP-03 - from cPrefixChoice_def and search_indexed_insert. *)
lemma search_mprefix_insert [cyphy_search_preparation]:
  "cPrefixChoice (insert e A) P =
    cExtChoice (cEventPrefix e (P e)) (cPrefixChoice A P :: 'e cyphyprocess)"
  by (simp only: cPrefixChoice_def search_indexed_insert)

lemmas [cyphy_refinement] = cSeq_mono cExtChoice_mono cEventPrefix_mono
  cSync_mono cInput_mono cOutput_mono cExtChoiceIdx_mono ax_parallel_mono ax_hide_mono ax_rename_mono ax_interrupt_mono

lemmas [mono_rule] = cPrefixChoice_mono cBoolGuard_mono cIntChoiceIdx_mono ax_parallel_mono ax_hide_mono ax_rename_mono ax_interrupt_mono

lemmas [cyphy_normalisation] = ax_mp_empty ax_mp_singleton ax_mp_seq
  ax_input_seq ax_output_seq ax_input_mprefix ax_mp_choice ax_mp_indexed
  cGuardedChoice_as_indexed ax_mprefix_parallel ax_hide_mprefix_disjoint ax_hide_mprefix_shared
  ax_rename_mprefix ax_interrupt_mprefix

lemmas [cyphy_search_preparation] = ax_mp_empty cPrefixChoice_empty

section \<open>Derived equality laws\<close>

(* ALG-01 - UCS p. 25, (2.7); p. 24, (2.3) *)
lemma cExtChoice_internal_left:
  "cExtChoice (sup P Q) R =
    sup (cExtChoice P R) (cExtChoice (Q :: 'e cyphyprocess) R)"
  by (simp only: ax_cExtChoice_comm ax_alg_ext_internal)

(* EC-03 / EC-04 - UCS p. 24, (2.5), (2.3) *)
lemma cExtChoice_left_commute:
  "cExtChoice P (cExtChoice Q R) = cExtChoice Q (cExtChoice P R)"
  by (metis ax_cExtChoice_assoc ax_cExtChoice_comm)

(* EC-02 / EC-03 - UCS p. 24, (2.1), (2.5) *)
lemma cExtChoice_left_idem:
  "cExtChoice P (cExtChoice P Q) = cExtChoice P Q"
  by (metis ax_cExtChoice_assoc ax_cExtChoice_idem)

(* Proved from cIntChoiceIdx_def and Isabelle/HOL SUP_cong. *)
lemma cIntChoiceIdx_cong:
  "(\<And>i. i \<in> I \<Longrightarrow> P i = Q i) \<Longrightarrow>
    cIntChoiceIdx I P = cIntChoiceIdx I Q"
  unfolding cIntChoiceIdx_def by (auto intro: SUP_cong)

(* Proved from cIntChoiceIdx_def and Isabelle/HOL image_image. *)
lemma cIntChoiceIdx_image:
  "cIntChoiceIdx (f ` I) P = cIntChoiceIdx I (\<lambda>i. P (f i))"
  by (simp add: cIntChoiceIdx_def image_image)

(* EC-01 - UCS p. 27, (2.16) *)
lemma cSlidingChoice_stop_left:
  "cSlidingChoice cStop P = P"
  by (simp add: cSlidingChoice_def ax_cExtChoice_stop_left)

(* HI-01 - UCS p. 96, (5.6); p. 95, (5.5) *)
lemma cHide_event_visible:
  "e \<notin> S \<Longrightarrow> cHide (cEventPrefix e P) S =
    cEventPrefix e (cHide (P :: 'e cyphyprocess) S)"
  using ax_hide_mprefix_disjoint[of "{e}" S "\<lambda>_. P"]
  by (simp add: cPrefixChoice_singleton)

(* HI-02 - UCS p. 96, (5.6); p. 95, (5.5) *)
lemma cHide_event_hidden:
  "e \<in> S \<Longrightarrow> cHide (cEventPrefix e P) S = cHide (P :: 'e cyphyprocess) S"
  using ax_hide_mprefix_shared[of "{e}" S "\<lambda>_. P"]
  by (simp add: cPrefixChoice_singleton cPrefixChoice_empty cIntChoiceIdx_singleton cSlidingChoice_stop_left)

(* HI-02 / HI-04 - UCS p. 96, (5.6) *)
lemma cHide_mprefix_all_hidden:
  assumes subset: "A \<subseteq> S"
  shows "cHide (cPrefixChoice A P) S =
    cIntChoiceIdx A (\<lambda>e. cHide (P e :: 'e cyphyprocess) S)"
proof (cases "A = {}")
  case True
  then show ?thesis by (simp add: cPrefixChoice_empty cIntChoiceIdx_empty ax_hide_stop)
next
  case False
  have inter: "A \<inter> S = A" and diff: "A - S = {}" using subset by auto
  show ?thesis using ax_hide_mprefix_shared[of A S P] False
    by (simp add: inter diff cPrefixChoice_empty cSlidingChoice_stop_left)
qed

(* MP-06 - UCS p. 27, (2.14) *)
lemma cExtChoiceIdx_event_mprefix:
  "cExtChoiceIdx I (\<lambda>i. cEventPrefix (f i) (P i)) =
    cPrefixChoice (f ` I) (\<lambda>e. cIntChoiceIdx {i \<in> I. e = f i}
      (P :: 'i \<Rightarrow> 'e cyphyprocess))"
proof -
  have domain: "(\<Union>i\<in>I. {f i}) = f ` I" by auto
  have "cExtChoiceIdx I (\<lambda>i. cEventPrefix (f i) (P i)) =
      cExtChoiceIdx I (\<lambda>i. cPrefixChoice {f i} (\<lambda>_. P i))"
    by (simp only: cPrefixChoice_singleton)
  also have "... = cPrefixChoice (f ` I)
      (\<lambda>e. cIntChoiceIdx {i \<in> I. e = f i} P)"
    by (simp only: ax_mp_indexed domain singleton_iff)
  finally show ?thesis .
qed

(* Proved from cPrefixChoice_def and cExtChoiceIdx_cong. *)
lemma cPrefixChoice_cong:
  "(\<And>e. e \<in> A \<Longrightarrow> P e = Q e) \<Longrightarrow> cPrefixChoice A P = cPrefixChoice A Q"
  unfolding cPrefixChoice_def by (rule cExtChoiceIdx_cong; simp)

(* CO-01 / MP-06 - UCS p. 27, (2.14) *)
lemma cInputPrefix_mprefix:
  assumes injective: "inj_on (prism_build c) A"
  shows "cInputPrefix c A (\<lambda>x. (\<lambda>_. b x, P x)) =
    cPrefixChoice (prism_build c ` {x \<in> A. b x})
      (\<lambda>e. P (inv_into A (prism_build c) e) :: 'e cyphyprocess)"
proof -
  have "cInputPrefix c A (\<lambda>x. (\<lambda>_. b x, P x)) =
      cPrefixChoice (prism_build c ` {x \<in> A. b x})
        (\<lambda>e. cIntChoiceIdx {x \<in> {x \<in> A. b x}. e = prism_build c x} P)"
    by (simp only: ax_input_mprefix[OF injective] cExtChoiceIdx_event_mprefix)
  also have "... = cPrefixChoice (prism_build c ` {x \<in> A. b x})
      (\<lambda>e. P (inv_into A (prism_build c) e))"
  proof (rule cPrefixChoice_cong)
    fix e assume "e \<in> prism_build c ` {x \<in> A. b x}"
    then obtain x where x: "x \<in> A" "b x" "e = prism_build c x" by auto
    have fibre: "{y \<in> {y \<in> A. b y}. e = prism_build c y} = {x}"
      using x injective by (auto dest: inj_onD)
    show "cIntChoiceIdx {x \<in> {x \<in> A. b x}. e = prism_build c x} P =
        P (inv_into A (prism_build c) e)"
      unfolding fibre
      by (simp only: cIntChoiceIdx_singleton x(3) inv_into_f_f[OF injective x(1)])
  qed
  finally show ?thesis .
qed

(* CO-01 / HI-02 - UCS p. 96, (5.6) *)
lemma cInputPrefix_all_hidden:
  assumes injective: "inj_on (prism_build c) A"
    and hidden: "prism_build c ` {x \<in> A. b x} \<subseteq> S"
  shows "cHide (cInputPrefix c A (\<lambda>x. (\<lambda>_. b x, P x))) S =
    cIntChoiceIdx {x \<in> A. b x} (\<lambda>x. cHide (P x :: 'e cyphyprocess) S)"
  unfolding cInputPrefix_mprefix[OF injective]
  apply (subst cHide_mprefix_all_hidden[OF hidden])
  apply (subst cIntChoiceIdx_image)
  apply (rule cIntChoiceIdx_cong)
  using injective by simp

(* MP-05 - UCS p. 27, (2.14) *)
lemma cEventPrefix_choice:
  "cExtChoice (cEventPrefix e P) (cEventPrefix f Q) =
    cPrefixChoice {e,f} (\<lambda>x. if x = e \<and> x = f then sup P Q
      else if x = e then P else Q :: 'e cyphyprocess)"
  using ax_mp_choice[of "{e}" "\<lambda>_. P" "{f}" "\<lambda>_. Q"]
  by (simp only: cPrefixChoice_singleton Int_iff singleton_iff Un_insert_left Un_empty_left;
      metis insert_commute)

(* MP-05 - UCS p. 27, (2.14) *)
lemma cEventPrefix_choice_mprefix:
  "cExtChoice (cEventPrefix e P) (cPrefixChoice B Q) =
    cPrefixChoice (insert e B) (\<lambda>x. if x = e \<and> x \<in> B then sup P (Q x)
      else if x = e then P else Q x :: 'e cyphyprocess)"
  using ax_mp_choice[of "{e}" "\<lambda>_. P" B Q]
  by (simp only: cPrefixChoice_singleton Int_iff singleton_iff Un_insert_left Un_empty_left)

(* MP-05 - UCS p. 27, (2.14) *)
lemma cPrefixChoice_choice_event:
  "cExtChoice (cPrefixChoice A P) (cEventPrefix e Q) =
    cPrefixChoice (insert e A) (\<lambda>x. if x \<in> A \<and> x = e then sup (P x) Q
      else if x \<in> A then P x else Q :: 'e cyphyprocess)"
  using ax_mp_choice[of A P "{e}" "\<lambda>_. Q"]
  by (simp only: cPrefixChoice_singleton Int_iff singleton_iff Un_insert_right Un_empty_right)

(* SY-01 - UCS p. 60, (3.10) *)
lemma cParallel_events:
  "cParallel S (cEventPrefix e P) (cEventPrefix f Q) =
    cExtChoice
      (cPrefixChoice ({e} - S) (\<lambda>_. cParallel S P (cEventPrefix f Q)))
      (cExtChoice
        (cPrefixChoice ({f} - S) (\<lambda>_. cParallel S (cEventPrefix e P) Q))
        (cPrefixChoice ({e} \<inter> {f} \<inter> S)
          (\<lambda>_. cParallel S P (Q :: 'e cyphyprocess))))"
  using ax_mprefix_parallel[of S "{e}" "\<lambda>_. P" "{f}" "\<lambda>_. Q"]
  by (simp only: cPrefixChoice_singleton)

(* SY-01 - UCS p. 60, (3.10) *)
lemma cParallel_event_mprefix:
  "cParallel S (cEventPrefix e P) (cPrefixChoice B Q) =
    cExtChoice
      (cPrefixChoice ({e} - S) (\<lambda>_. cParallel S P (cPrefixChoice B Q)))
      (cExtChoice
        (cPrefixChoice (B - S) (\<lambda>x. cParallel S (cEventPrefix e P) (Q x)))
        (cPrefixChoice ({e} \<inter> B \<inter> S)
          (\<lambda>x. cParallel S P (Q x :: 'e cyphyprocess))))"
  using ax_mprefix_parallel[of S "{e}" "\<lambda>_. P" B Q]
  by (simp only: cPrefixChoice_singleton)

(* SY-01 - UCS p. 60, (3.10) *)
lemma cParallel_mprefix_event:
  "cParallel S (cPrefixChoice A P) (cEventPrefix e Q) =
    cExtChoice
      (cPrefixChoice (A - S) (\<lambda>x. cParallel S (P x) (cEventPrefix e Q)))
      (cExtChoice
        (cPrefixChoice ({e} - S) (\<lambda>_. cParallel S (cPrefixChoice A P) Q))
        (cPrefixChoice (A \<inter> {e} \<inter> S)
          (\<lambda>x. cParallel S (P x) (Q :: 'e cyphyprocess))))"
  using ax_mprefix_parallel[of S A P "{e}" "\<lambda>_. Q"]
  by (simp only: cPrefixChoice_singleton)

subsection \<open>Derived finite-prefix laws\<close>

(* FP-02 (derived) - Oliveira p. 206, C.102; TPC p. 79, (3.5) *)
lemma cHide_event_skip [cyphy_normalisation]:
  "e \<in> H \<Longrightarrow> cHide (cEventPrefix e cSkip) H = (cSkip :: 'e cyphyprocess)"
  by (simp add: cHide_event_hidden ax_hide_skip)

(* FP-04 (derived) - Oliveira p. 210, C.125; TPC p. 79, (3.5) *)
lemma cHide_factor_visible_event:
  "e \<notin> H \<Longrightarrow>
    cSeq (cEventPrefix e cSkip) (cHide P H) =
    cHide (cSeq (cEventPrefix e cSkip) (P :: 'e cyphyprocess)) H"
  by (simp add: ax_cSeq_event_prefix ax_cSeq_skip_left cHide_event_visible)

(* FP-05 (derived) - UCS p. 60, (3.10), singleton specialisation *)
lemma cParallel_event_sync [cyphy_normalisation]:
  "e \<in> S \<Longrightarrow>
    cParallel S (cEventPrefix e P) (cEventPrefix e Q) =
    cEventPrefix e (cParallel S P (Q :: 'e cyphyprocess))"
  by (simp add: cParallel_events cPrefixChoice_empty cPrefixChoice_singleton
      ax_cExtChoice_stop_left)

(* FP-06 (derived) - Oliveira p. 203, C.84; from SY-01 *)
lemma cParallel_event_step [cyphy_normalisation]:
  assumes "e \<notin> S" "B \<subseteq> S"
  shows "cParallel S (cEventPrefix e P) (cPrefixChoice B Q) =
    cEventPrefix e (cParallel S P (cPrefixChoice B (Q :: 'e \<Rightarrow> 'e cyphyprocess)))"
proof -
  have left: "{e} - S = {e}" and right: "B - S = {}"
    and shared: "{e} \<inter> B \<inter> S = {}"
    using assms by auto
  show ?thesis
    by (simp only: cParallel_event_mprefix left right shared cPrefixChoice_empty cPrefixChoice_singleton
        ax_cExtChoice_stop_left ax_cExtChoice_stop_right)
qed

(* FP-07 (derived) - Oliveira p. 203, C.83 *)
lemma cHide_parallel_event_sync [cyphy_normalisation]:
  assumes "e \<in> S" "e \<in> H"
  shows "cHide (cParallel S (cEventPrefix e P) (cEventPrefix e Q)) H =
    cHide (cParallel S P (Q :: 'e cyphyprocess)) H"
  using assms by (simp add: cParallel_event_sync cHide_event_hidden)

(* FP-08 (derived) - UCS p. 96, (5.6); outward form of HI-01 *)
lemma cHide_factor_event:
  "e \<notin> H \<Longrightarrow>
    cEventPrefix e (cHide P H) = cHide (cEventPrefix e (P :: 'e cyphyprocess)) H"
  by (simp add: cHide_event_visible)

(* FP-08 (derived) - UCS p. 96, (5.6); outward form of HI-01 *)
lemma cHide_factor_mprefix:
  "A \<inter> H = {} \<Longrightarrow>
    cPrefixChoice A (\<lambda>e. cHide (P e) H) = cHide (cPrefixChoice A (P :: 'e \<Rightarrow> 'e cyphyprocess)) H"
  by (simp only: ax_hide_mprefix_disjoint)

(* ALG-03 - UCS p. 95, (5.1) *)
lemma cHide_factor_internal_choice:
  "sup (cHide P H) (cHide Q H) = cHide (sup P (Q :: 'e cyphyprocess)) H"
  by (simp only: ax_alg_hide_internal)

subsection \<open>Hiding, parallel and exception axioms with their derived laws\<close>

(* HI-07 - Oliveira p. 210, C.125 *)
axiomatization where
  ax_hide_seq_unit:
    "cHide (cSeq P Q) H = cSeq (cHide P H) (cHide (Q :: 'e cyphyprocess) H)" and
  (* HI-08 - Oliveira p. 210, C.127 *)
  ax_hide_parallelAct_unit:
    "S \<inter> H = {} \<Longrightarrow>
      cHide (cParallelAct 0\<^sub>L 0\<^sub>L S P Q) H =
      cParallelAct 0\<^sub>L 0\<^sub>L S (cHide P H) (cHide (Q :: 'e cyphyprocess) H)"

(* HI-07 - Oliveira p. 210, C.125 *)
lemma cHide_factor_seq:
  "cSeq (cHide P H) (cHide Q H) = cHide (cSeq P (Q :: 'e cyphyprocess)) H"
  by (simp only: ax_hide_seq_unit)

(* HI-08 - Oliveira p. 210, C.127 *)
lemma cHide_factor_parallelAct_unit:
  "S \<inter> H = {} \<Longrightarrow>
    cParallelAct 0\<^sub>L 0\<^sub>L S (cHide P H) (cHide Q H) =
    cHide (cParallelAct 0\<^sub>L 0\<^sub>L S P (Q :: 'e cyphyprocess)) H"
  by (simp only: ax_hide_parallelAct_unit)

(* SY-04 - TPC p. 69, (2.10) *)
axiomatization where
  ax_parallelAct_unit_mprefix:
    "cParallelAct 0\<^sub>L 0\<^sub>L S (cPrefixChoice A P) (cPrefixChoice B Q) =
      cExtChoice
        (cPrefixChoice (A - S) (\<lambda>e. cParallelAct 0\<^sub>L 0\<^sub>L S (P e) (cPrefixChoice B Q)))
        (cExtChoice
          (cPrefixChoice (B - S) (\<lambda>e. cParallelAct 0\<^sub>L 0\<^sub>L S (cPrefixChoice A P) (Q e)))
          (cPrefixChoice (A \<inter> B \<inter> S)
            (\<lambda>e. cParallelAct 0\<^sub>L 0\<^sub>L S (P e) (Q e :: 'e cyphyprocess))))"

(* SY-04 - TPC p. 69, (2.10) *)
lemma cParallelAct_unit_events:
  "cParallelAct 0\<^sub>L 0\<^sub>L S (cEventPrefix e P) (cEventPrefix f Q) =
    cExtChoice
      (cPrefixChoice ({e} - S) (\<lambda>_. cParallelAct 0\<^sub>L 0\<^sub>L S P (cEventPrefix f Q)))
      (cExtChoice
        (cPrefixChoice ({f} - S) (\<lambda>_. cParallelAct 0\<^sub>L 0\<^sub>L S (cEventPrefix e P) Q))
        (cPrefixChoice ({e} \<inter> {f} \<inter> S)
          (\<lambda>_. cParallelAct 0\<^sub>L 0\<^sub>L S P (Q :: 'e cyphyprocess))))"
  using ax_parallelAct_unit_mprefix[of S "{e}" "\<lambda>_. P" "{f}" "\<lambda>_. Q"]
  by (simp only: cPrefixChoice_singleton)

(* FP-09 (derived) - Oliveira p. 207, C.106 *)
lemma cParallelAct_unit_event_sync:
  "e \<in> S \<Longrightarrow>
    cParallelAct 0\<^sub>L 0\<^sub>L S (cEventPrefix e P) (cEventPrefix e Q) =
    cEventPrefix e (cParallelAct 0\<^sub>L 0\<^sub>L S P (Q :: 'e cyphyprocess))"
  by (simp add: cParallelAct_unit_events cPrefixChoice_empty cPrefixChoice_singleton
      ax_cExtChoice_stop_left)

(* EX-01 - UCS p. 140, (7.6) *)
axiomatization where
  ax_exception_mprefix:
    "cException (cPrefixChoice A P) B Q =
      cPrefixChoice A (\<lambda>e. if e \<in> B then Q else cException (P e) B (Q :: 'e cyphyprocess))" and
  (* EX-01 - UCS p. 140, (7.6); AFP HOL-CSPM Throw_STOP *)
  ax_exception_stop:
    "cException cStop B Q = (cStop :: 'e cyphyprocess)" and
  (* EX-01 - UCS p. 140, (7.6); AFP HOL-CSPM Throw_SKIP *)
  ax_exception_skip:
    "cException cSkip B Q = (cSkip :: 'e cyphyprocess)"

(* RF-08 - UCS p. 233, Theorem 10.1 *)
axiomatization where
  ax_exception_mono [mono_rule, cyphy_refinement]:
    "P' \<le> P \<Longrightarrow> Q' \<le> Q \<Longrightarrow>
      cException P' B Q' \<le> cException P B (Q :: 'e cyphyprocess)"

(* EX-01 - UCS p. 140, (7.6) *)
lemma cException_event:
  "cException (cEventPrefix e P) B Q =
    cEventPrefix e (if e \<in> B then Q else cException P B (Q :: 'e cyphyprocess))"
  using ax_exception_mprefix[of "{e}" "\<lambda>_. P" B Q]
  by (simp only: cPrefixChoice_singleton)

subsection \<open>Discrete initial timeout and start deadline\<close>

(* Proved from cTPrefix_def, MO-01, MO-02 and Isabelle/HOL lfp_mono. *)
lemma cTPrefix_mono [mono_rule]:
  "P\<^sub>1 \<le> P\<^sub>2 \<Longrightarrow> cTPrefix P\<^sub>1 \<le> cTPrefix P\<^sub>2"
  unfolding cTPrefix_def
  by (rule lfp_mono, rule cExtChoice_mono, assumption, rule order_refl)

(* TM-01 - Wei p. 5, Definition 2; p. 15, (45), Definition 11; proved from cInitialTimeout1_def, MO-01 and MO-02 *)
lemma ax_initialTimeout1_unit_mono [mono_rule, cyphy_refinement]:
  "P' \<le> P \<Longrightarrow> Q' \<le> Q \<Longrightarrow>
    cInitialTimeout1 P' Q' \<le> cInitialTimeout1 P (Q :: 'e::tock cyphyprocess)"
  unfolding cInitialTimeout1_def
  by (rule cExtChoice_mono, assumption, rule cEventPrefix_mono, assumption)

(* TM-02 - Wei p. 5, Definition 2; p. 16, (53); proved from the equations of cStartDeadline, MO-01 and MO-02 *)
lemma ax_startDeadline_unit_mono [mono_rule, cyphy_refinement]:
  "P' \<le> P \<Longrightarrow>
    cStartDeadline d P' \<le> cStartDeadline d (P :: 'e::tock cyphyprocess)"
  by (induct d) (simp_all add: cExtChoice_mono cEventPrefix_mono)

subsection \<open>Maximal progress and priority\<close>

(* PR-02 - Wei p. 15, (40) *)
axiomatization where
  ax_prioritise_hide:
    "cPrioritise V (cHide P H) =
      cHide (cPrioritise (V \<union> H) (P :: 'e cyphyprocess)) H"

(* PR-05 - UCS p. 488; robochart-csp-gen core_timed.csp, TimeOut_1 *)
axiomatization where
  ax_prioritise_initialTimeout1_disjoint:
    "A \<inter> V = {} \<Longrightarrow> cPrioritise V (cInitialTimeout1 (cPrefixChoice A P) Q) =
      cInitialTimeout1 (cPrefixChoice A (\<lambda>e. cPrioritise V (P e)))
        (cPrioritise V (Q :: 'e::tock cyphyprocess))"

(* PR-06 - tick-tock-CSP FL Pri_ExtChoice_two_prefixes; robochart-csp-gen core_timed.csp, TimeOut_1 and StartBy *)
axiomatization where
  ax_prioritise_initialTimeout1_urgent:
    "A \<inter> V \<noteq> {} \<Longrightarrow> cPrioritise V (cInitialTimeout1 (cPrefixChoice A P) Q) =
      cStartDeadline 0 (cPrefixChoice A (\<lambda>e. cPrioritise V (P e :: 'e::tock cyphyprocess)))"

declare [[literal_variables]]

(* notation useq (infixr ";" 55) *) \<comment> \<open>this conflicts with Isabelle's let syntax\<close> 

syntax "_useq_iter" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (";_/\<in>_. _" [0, 0, 10] 10)

end