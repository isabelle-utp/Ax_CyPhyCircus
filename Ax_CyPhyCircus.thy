theory Ax_CyPhyCircus
  imports 
    "UTP2.utp" 
    "Circus_Toolkit.Channels_Events"
    "Circus_Toolkit.Action_Command"
    "Abstract_Prog_Syntax.Abstract_Prog_Syntax"
    "Framed_ODEs.Framed_ODEs"
begin

unbundle UTP_Syntax

no_notation disj  (infixr \<open>|\<close> 30)
no_notation funcset (infixr "\<rightarrow>" 60)

subsection \<open> Types and Constants \<close>

typedecl ('e, 's) "action"

type_synonym 'e process = "('e, unit) action"

type_synonym ('a, 'e) chan = "'a \<Longrightarrow>\<^sub>\<triangle> 'e"

subsection \<open> Circus Operators \<close>

axiomatization  
  cAssigns :: "('s \<Rightarrow> 's) \<Rightarrow> ('e, 's) action" and 
  cSeq :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" and
  cMPrefix :: "('s \<Rightarrow> 'e set) \<Rightarrow> ('e \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" and
  cGuard :: "(bool, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" and
  cIChoice :: "'i set \<Rightarrow> ('i \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" and
  cEChoice :: "'i set \<Rightarrow> ('i \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" and 
  cRenaming :: "('e \<leftrightarrow> 'f) \<Rightarrow> ('e, 's) action \<Rightarrow> ('f, 's) action" and
  cHide :: "('e, 's) action \<Rightarrow> 'e set \<Rightarrow> ('e, 's) action" and
  cParallel :: "('e, 's) action \<Rightarrow> 'e set \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" and
  cProcess :: "('e, 's) action \<Rightarrow> 'e process" and
  cAssume :: "('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) action" and
  cInterEvent :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" (infixl "\<triangle>" 55) 

adhoc_overloading useq == cSeq

adhoc_overloading uassigns == cAssigns

definition Skip :: "('e, 's) action" where
"Skip = cAssigns id"

definition Chaos :: "('e, 's) action" where
"Chaos = cIChoice (UNIV::int set) (\<lambda> i. Skip)"

definition Miracle :: "('e, 's) action" where
"Miracle = cIChoice ({}::bool set) (\<lambda> i. Skip)"

definition Stop :: "('e, 's) action" where
"Stop = cEChoice ({}::bool set) (\<lambda> i. Skip)"

definition cichoice :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow>
 ('e, 's) action" (infixl "\<sqinter>" 59) where
  "cichoice P Q = cIChoice {True, False} (\<lambda> b. if b then P else Q)"

definition cechoice :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow>
 ('e, 's) action" (infixl "\<box>" 59) where
  "cechoice P Q = cEChoice {True, False} (\<lambda> b. if b then P else Q)"

definition cInterleave (infixl "\<interleave>" 59) where "cInterleave P Q = cParallel P {} Q" 

definition cPrefix :: "('a, 'e) chan \<Rightarrow> ('a \<Rightarrow> (('s \<Rightarrow> bool) \<times> ('e, 's) action)) \<Rightarrow> ('e, 's) action" where
"cPrefix c P = cMPrefix (\<lambda> s. {e. e \<in> range (build\<^bsub>c\<^esub>) \<and> fst (P (the (match\<^bsub>c\<^esub> e))) s}) (snd \<circ> P \<circ> the \<circ> match\<^bsub>c\<^esub>)"

definition cInput :: "('a, 'e) chan \<Rightarrow> ('a \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where
"cInput c A = cPrefix c (\<lambda> v. ((\<lambda> s. True), A v))"

definition cSync :: "(unit, 'e) chan \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" where
"cSync c A = cPrefix c (\<lambda> v. (\<lambda> s. True, A))"

definition cOutput :: "('a, 'e) chan \<Rightarrow> ('a, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" where
"cOutput c e A = cPrefix c (\<lambda> v::'a. ((\<lambda> s::'s. v = e(s)), A))"

definition coutinp :: "('a \<times> 'b, 'e) chan \<Rightarrow> ('a, 's) expr  \<Rightarrow> ('b \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where 
"coutinp c e A = cPrefix c (\<lambda> (x, y). (\<lambda> s. x = e(s), A y))"

definition cdotinp :: "('a \<times> 'b, 'e) chan \<Rightarrow> ('a, 's) expr  \<Rightarrow> ('b \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where 
"cdotinp c e A = cPrefix c (\<lambda> (x, y). (\<lambda> s. x = e(s), A y))"

definition cdotdot :: "('a \<times> 'b, 'e) chan \<Rightarrow> ('a, 's) expr \<Rightarrow> ('b, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" where 
"cdotdot c e1 e2 A = cPrefix c (\<lambda> (x, y). (\<lambda> s. x = e1(s) \<and> y = e2(s), A))"

definition cdotdotinp :: "('a \<times> 'b \<times> 'c, 'e) chan \<Rightarrow>('a, 's) expr \<Rightarrow> ('b, 's) expr  \<Rightarrow> ('c \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where 
"cdotdotinp c e1 e2 A = cPrefix c (\<lambda> (x, y, z). (\<lambda> s. x = e1(s) \<and> y = e2(s), A z))"

definition cdotdotout :: "('a \<times> 'b \<times> 'c, 'e) chan \<Rightarrow>('a, 's) expr \<Rightarrow> ('b, 's) expr \<Rightarrow>('c, 's) expr  \<Rightarrow>  ('e, 's) action \<Rightarrow> ('e, 's) action" where 
"cdotdotout c e1 e2 e3 A = cPrefix c (\<lambda> (x, y, z). (\<lambda> s. x = e1(s) \<and> y = e2(s)  \<and> z = e3(s), A))"

definition cdotdotdotinp :: "('a \<times> 'b \<times> 'c \<times> 'd, 'e) chan \<Rightarrow>('a, 's) expr \<Rightarrow> ('b, 's) expr   \<Rightarrow> ('c, 's) expr \<Rightarrow> ('d \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where 
"cdotdotdotinp c e1 e2 e3 A = cPrefix c (\<lambda> (x, y, z, w). (\<lambda> s. x = e1(s) \<and> y = e2(s) \<and> z = e3(s), A w))"

definition cdotdotdotout :: "('a \<times> 'b \<times> 'c \<times> 'd, 'e) chan \<Rightarrow>('a, 's) expr \<Rightarrow> ('b, 's) expr   \<Rightarrow> ('c, 's) expr \<Rightarrow>('d, 's) expr \<Rightarrow>  ('e, 's) action \<Rightarrow> ('e, 's) action" where 
"cdotdotdotout c e1 e2 e3 e4 A = cPrefix c (\<lambda> (x, y, z, w). (\<lambda> s. x = e1(s) \<and> y = e2(s) \<and> z = e3(s) \<and> w = e4(s), A ))"

bundle Circus_Syntax
begin

unbundle Expression_Syntax

no_notation disj (infixr "|" 30)
no_notation conj (infixr "&" 35)
no_notation funcset (infixr "\<rightarrow>" 60)

no_syntax
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /\<mapsto>/ _")
  ""         :: "maplet \<Rightarrow> updbind"              ("_")
  ""         :: "maplet \<Rightarrow> maplets"             ("_")
  "_Maplets" :: "[maplet, maplets] \<Rightarrow> maplets" ("_,/ _")
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"           ("(1[_])")


end

syntax 
 \<comment> \<open> "_cseq" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ ; _" [50, 51] 50) 
    no need to define cseq syntax, cseq is overloading useq
  "_cinterrupt" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<triangle> _" [50, 51] 50)
  (*Can interrupt be defined using definition, just like cechoice??*)\<close>

  "_cinput" :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>?_ \<rightarrow> _" [61, 0, 62] 62)

  "_coutput" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>!_ \<rightarrow> _" [61, 0, 62] 62)

  "_cdot" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>._ \<rightarrow> _" [61, 0, 62] 62)
  \<comment> \<open>_._ is parsed as a whole, so bolded here to avoid conflict\<close>

  "_coutinp" :: "id \<Rightarrow> logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>!_\<^bold>?_ \<rightarrow> _" [61, 0, 0, 62] 62)

  "_cdotinp" :: "id \<Rightarrow> logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>?_ \<rightarrow> _" [61, 200, 200, 62] 62)


  "_cdotdot" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>._ \<rightarrow> _" [61, 200, 200, 62] 62)


  "_cdotdotinp" :: "id \<Rightarrow> logic   \<Rightarrow> logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>._\<^bold>?_ \<rightarrow> _" [61, 200,200, 200, 62] 62)


  "_cdotdotout" :: "id \<Rightarrow> logic   \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>._\<^bold>!_ \<rightarrow> _" [61, 200,200, 200, 62] 62)

  "_cdotdotdotinp" :: "id \<Rightarrow> logic \<Rightarrow> logic  \<Rightarrow> logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>._\<^bold>._\<^bold>?_ \<rightarrow> _" [61, 200,200,200, 200, 62] 62)

  "_cdotdotdotout" :: "id \<Rightarrow> logic \<Rightarrow> logic  \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>._\<^bold>._\<^bold>!_ \<rightarrow> _" [61, 200,200,200,200, 62] 62)

  "_csync" :: "id \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow> _" [61, 62] 61)
  "_cguard" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<^bold>& _" [60, 61] 60)

  \<comment> \<open>the order of the parameters does not need to match the definition.\<close>
  "_crenaming" :: "logic \<Rightarrow> rnenum \<Rightarrow> logic" ("_ [_]" [60, 0] 60)  

  "_chide" :: "logic \<Rightarrow> chans \<Rightarrow> logic" ("_ \<Zhide> \<lbrace>_\<rbrace>" [60, 61] 60)
  "_chidecs" :: "logic \<Rightarrow> id \<Rightarrow> logic" ("_ \<Zhide> _" [60, 61] 60)(*TBC to hide a channelset cs?*)

  "_cparallel" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<lbrakk> | _ | \<rbrakk> _" [60, 0,  61] 60)
 
  "_cEChoice" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<box> _ \<in> _ \<bullet> _")

  "_cInterleave" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<interleave> _ \<in> _ \<bullet> _" [0, 0, 10] 10) 
  \<comment> \<open>\<interleave> i\<in>{1..inpSize} \<bullet> NodeIn(l,n,i)\<close>
  
  "_cseqIte" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (";; _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  \<comment> \<open>;; i\<in>{1..inpSize} \<bullet> NodeIn(l,n,i)\<close>

  "_cParallelIte" :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrakk> _ \<rbrakk> _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  
  "_cParam" :: "pttrn \<Rightarrow>  logic \<Rightarrow> logic" ("_ \<bullet> _" [10, 0] 10)(*TBC*) 

translations 
  "_cinput c x  P" == "CONST cInput c (\<lambda> x. P)"
  "_coutput c e P" == "CONST cOutput c (e)\<^sub>e P"
  "_coutinp c e x P" == "CONST coutinp c (e)\<^sub>e (\<lambda> x. P)"
  "_cdotinp c e x P" == "CONST cdotinp c (e)\<^sub>e (\<lambda> x. P)"

  "_cdotdot c e1 e2 P" == "CONST cdotdot c (e1)\<^sub>e (e2)\<^sub>e P" 
  "_cdotdotinp c e1 e2 x P" == "CONST cdotdotinp c  (e1)\<^sub>e (e2)\<^sub>e (\<lambda> x. P)"

  "_cdotdotout c  e1 e2 e3 P" == "CONST cdotdotout c  (e1)\<^sub>e (e2)\<^sub>e (e3)\<^sub>e P" 
  "_cdotdotdotinp c  e1 e2 e3 x P" == "CONST cdotdotdotinp c  (e1)\<^sub>e (e2)\<^sub>e (e3)\<^sub>e (\<lambda> x. P)"  

  "_cdotdotdotout c  e1 e2 e3 e4 P" == "CONST cdotdotdotout c  (e1)\<^sub>e (e2)\<^sub>e (e3)\<^sub>e (e4)\<^sub>e P" 

  "_cguard b P" == "CONST cGuard (b)\<^sub>e P"
  "_cdot c e P" == "CONST cOutput c (e)\<^sub>e P"
  "_csync c P" == "CONST cSync c P"
  "_crenaming P rn" == "CONST cRenaming (_rnenum rn) P" 
  "_chide P es" == "CONST cHide P (_ch_enum es)" 
  "_cparallel P A Q" == "CONST cParallel P A Q " 
  "_cEChoice i A P" == "CONST cEChoice A (\<lambda> i. P)"
  "_cInterleave i A P" == "CONST cInterleave A (\<lambda> i. P)"

subsection \<open> Continuous Operators \<close>

axiomatization
  cEvol :: "('a \<Longrightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) action" and
  cInterCond :: "('e, 's) action \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('e, 's) action" 
where
  cEvol_cInterCond: "cInterCond (cEvol a e p) q = cEvol a e (p \<and> \<not> q)" and
  cEvol_assumeI: "cEvol a e p = cEvol a e p ;; cAssume (\<not> p)"

syntax
  "_cEvol"        :: "derivs \<Rightarrow> logic \<Rightarrow> logic" ("[\<Lambda> _ | _ ]")
  "_cEvol_nopred" :: "derivs \<Rightarrow> logic" ("[\<Lambda> _ ]")

translations
  "_cEvol \<sigma> G" => "CONST cEvol (_smaplets_svids \<sigma>) (_Subst \<sigma>) (G)\<^sub>e"
  "_cEvol_nopred e" == "_cEvol e (CONST True)"
  "_cEvol (_SDeriv \<sigma>) G" <= "CONST cEvol a (_Subst \<sigma>) (G)\<^sub>e"

(* Test *)

term "a\<^bold>?x \<rightarrow> [\<Lambda> y` = x]"

end