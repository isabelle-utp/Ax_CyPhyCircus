theory Ranger_CyPhyCircus
  imports Ax_CyPhyCircus
begin

declare [[literal_variables]]

consts
  targetPos    :: real
  targetRadius :: real
  eps          :: real
  timeStep     :: real

chantype RangerChannels =
  target          :: unit
  getPos          :: real
  getVel          :: real
  setVel          :: real
  targetTriggered :: bool
  proceed         :: unit

definition triggerChan :: "RangerChannels set" where
"triggerChan = \<lbrace>targetTriggered\<rbrace>"

alphabet RangerState = 
  pos        :: real
  vel        :: real
  stepTimer  :: real
  targetTrig :: bool

definition Movement :: "(RangerChannels, RangerState) cyphyaction" where
"Movement = [\<Lambda> pos` = vel, vel` = 0, stepTimer` = 1] \<triangle>\<^sub>p (stepTimer \<ge> timeStep)"

definition InputTriggers :: "(RangerChannels, RangerState) cyphyaction" where
  "InputTriggers = 
    if abs(pos - targetPos) \<le> targetRadius - eps \<rightarrow> targetTriggered\<^bold>!True \<rightarrow> Skip
    |  abs(pos - targetPos) \<ge> targetRadius \<rightarrow> targetTriggered\<^bold>!False \<rightarrow>Skip
    |  (abs(pos-targetPos) \<ge> targetRadius - eps \<and> abs(pos - targetPos) \<le> targetRadius) \<rightarrow> Skip
    fi"

definition GetVars :: "(RangerChannels, RangerState) cyphyaction" where
  "GetVars = getPos\<^bold>!pos \<rightarrow> Skip \<box> getVel\<^bold>!vel \<rightarrow> Skip"

definition SetVars :: "(RangerChannels, RangerState) cyphyaction" where
  "SetVars = getPos\<^bold>?x \<rightarrow> (pos := x) \<box> setVel\<^bold>?x \<rightarrow> (vel := x)"

recursive QueryUpdate :: "(RangerChannels, RangerState) cyphyaction" 
  where "QueryUpdate = ((GetVars \<box> SetVars) ;; QueryUpdate) \<box> proceed \<rightarrow> Skip"

definition "EventBuffer = targetTrig := False ;; (\<mu> X. (targetTriggered\<^bold>?b \<rightarrow> targetTrig := b
                                                        \<box> 
                                                        (targetTrig = True) \<^bold>& target \<rightarrow> Skip) ;; X)"

recursive where "RangerLoop = stepTimer := 0 ;; Movement ;; InputTriggers ;; (QueryUpdate \<triangle>[0] Skip) ;; RangerLoop"

definition "envVars = id_lens"

definition "MainAction = RangerLoop \<lbrakk>envVars | triggerChan | \<^bold>0\<rbrakk> EventBuffer"

end