section \<open> RoboWorld CyPhyCircus Semantics \<close>

theory Ranger_Kinematics_RoboWorld
  imports "Axiomatic_CyPhyCircus.Ax_CyPhyCircus"
begin

subsection \<open> Rotating Vectors \<close>

abbreviation (input) e1 :: "real^2" where "e1 \<equiv> axis 1 1"
abbreviation (input) e2 :: "real^2" where "e2 \<equiv> axis 2 1"

lemma nat_of_2_2 [simp]: "(nat_of (2 :: 2)) = 0"
  by (metis exhaust_2 nat_of_0 rel_simps(93))

text \<open> Anticlockwise 90 degree turn \<close>

definition rot90 :: "real^2 \<Rightarrow> real^2" where
  "rot90 v = (inner v e1) *\<^sub>R e2 - (inner v e2) *\<^sub>R e1"  

lemma rot90_Vec: "rot90 V[x, y] = V[y, -x]"
  by (simp add: rot90_def axis_Vec inner_Vec scaleR_Vec minus_Vec numeral_2_eq_2 ezlist_def)

lemma rot90_Vec': "rot90 x = Vector[x $ 1, - x $ 0]"
  apply (cases rule: Vec2_caseE[of x])
  apply (simp add: rot90_Vec Vec_lookup')
  done

definition atan2 :: "real \<Rightarrow> real \<Rightarrow> real" where
"atan2 y x = (
  if x > 0 then 
    arctan (y / x)
  else if x < 0 \<and> y \<ge> 0 then 
    arctan (y / x) + pi
  else if x < 0 \<and> y < 0 then 
    arctan (y / x) - pi
  else if x = 0 \<and> y > 0 then 
    pi / 2
  else if x = 0 \<and> y < 0 then 
    - (pi / 2)
  else 
    0)"

definition vec_angle :: "real vec[2] \<Rightarrow> real" where
"vec_angle v = atan2 (v$1) (v$0)"

subsection \<open> Channels \<close>

datatype InOut = "in" | "out"

chantype RobotChan =   
  getRobotPosition            :: "real vec[2]"
  getRobotVelocity            :: "real vec[2]"
  getRobotAcceleration        :: "real vec[2]"
  getRobotAngles              :: "real"
  getRobotAngularVelocity     :: "real"
  getRobotAngularAcceleration :: "real"
  setRobotVelocity            :: "real vec[2]"
  setRobotAcceleration        :: "real vec[2]"
  setRobotAngularVelocity     :: real
  setRobotAngularAcceleration :: real
  obstacle                    :: InOut
  stop                        :: InOut
  moveCall                    :: "real \<times> real"
  obstacleTriggered           :: bool

subsection \<open> Environment \<close>

consts
  maxAccel          :: real
  maxVel            :: real
  maxAngVel         :: real
  maxBrake          :: real
  targetPos         :: "real vec[2]"
  targetRadius      :: real
  timeStep          :: real
  obstaclePositions :: "(real vec[2] ) set"
  collisionRadius   :: real
  detectionRadius   :: real

subsubsection \<open> Environment State \<close>

alphabet EnvironmentState = 
  linAccel   :: real
  pos        :: "real vec[2]"
  orient     :: "real vec[2]"
  linVel     :: real
  angVel     :: real
  angRadius  :: real
  stepTimer  :: real
  targetTrig :: bool

expression EnvironmentState_inv is 
  "0 \<le> linVel \<and> linVel \<le> maxVel \<and> stepTimer \<le> timeStep"

expression vel is "linVel *\<^sub>R orient"
expression accel is "(linAccel *\<^sub>R orient) + ((linVel * angVel) *\<^sub>R rot90 orient)"
expression ang is "vec_angle orient"
expression angAcc is "if angRadius = 0 then 0 else linAccel / angRadius"

subsubsection \<open> Robot Movement \<close>

definition Movement :: "(RobotChan, EnvironmentState) cyphyaction" where
"Movement = [\<Lambda> pos` = linVel *\<^sub>R orient, linVel` = linAccel
            ,  orient` = angVel *\<^sub>R rot90(orient), linAccel` = 0
            ,  angVel` = angAcc
            ,  stepTimer` = 1 
            | 0 \<le> linVel \<and> linVel \<le> maxVel \<and> stepTimer \<le> timeStep]"

subsubsection \<open> Update Actions that interrupt Robot Movement \<close>

definition
  "CollisionDetection = 
    ((\<exists> obs \<in> obstaclePositions. \<parallel>pos - obs\<parallel> < collisionRadius) \<^bold>&
      (linVel, linAccel) := (0, 0))
    \<box> 
    ((\<not> (\<exists> obs \<in> obstaclePositions. \<parallel>pos - obs\<parallel> < collisionRadius)) \<^bold>&
      Skip)"

definition "EnvironmentUpdate = CollisionDetection"

subsubsection \<open> Communication Actions that occur on the time step \<close>

definition
  "Obstacle_InEventMapping = 
    ((\<exists> obs \<in> obstaclePositions. norm (pos - obs) < detectionRadius) \<^bold>&
      (obstacleTriggered\<^bold>!True \<rightarrow> Skip))
    \<box>
    ((\<not> (\<exists> obs \<in> obstaclePositions. norm (pos - obs) < detectionRadius)) \<^bold>&
      (obstacleTriggered\<^bold>!False \<rightarrow> Skip))"

definition "InputTriggers = Obstacle_InEventMapping"

definition "GetPosition = getRobotPosition\<^bold>!pos \<rightarrow> Skip"
definition "GetVelocity = getRobotVelocity\<^bold>!vel \<rightarrow> Skip"
definition "GetAcceleration = getRobotAcceleration\<^bold>!accel \<rightarrow> Skip"
definition "GetAngles = getRobotAngles\<^bold>!ang \<rightarrow> Skip"
definition "GetAngularVel = getRobotAngularVelocity\<^bold>!angVel \<rightarrow> Skip"
definition "GetAngularAcc = getRobotAngularAcceleration\<^bold>!angAcc \<rightarrow> Skip"

definition "SetVelocity = 
  setRobotVelocity\<^bold>?newVel \<rightarrow> (linVel := \<parallel>newVel\<parallel> ;; 
                              orient := (if \<parallel>newVel\<parallel> = 0 then 0 else newVel /\<^sub>R \<parallel>newVel\<parallel>))"
definition "SetAcceleration = 
  setRobotAcceleration\<^bold>?newAcc \<rightarrow> (linAccel := newAcc \<bullet> orient ;; 
                                  angVel := (newAcc \<bullet> rot90 orient) / linVel)"
definition "SetAngularVel = setRobotAngularVelocity\<^bold>?newAngVel \<rightarrow> angVel := newAngVel"
definition "SetAngularAcc = setRobotAngularAcceleration\<^bold>?newAngAcc \<rightarrow> Skip"

definition 
  "GetSetVariables = 
    GetPosition \<interleave> GetVelocity \<interleave> GetAcceleration \<interleave> 
    GetAngles \<interleave> GetAngularVel \<interleave> GetAngularAcc \<interleave> 
    SetVelocity \<interleave> SetAcceleration \<interleave> SetAngularVel \<interleave> SetAngularAcc"

recursive where "Communication = InputTriggers ;; (GetSetVariables ;; Communication)"

subsubsection \<open> Input Event Buffers \<close>

definition
  "Obstacle_Buffer = 
    (var obstacleTrig :: bool. 
      obstacleTrig := False ;;
      (\<mu> X.(  
        obstacleTriggered\<^bold>?b \<rightarrow> (obstacleTrig := b)
        \<box>
        ((obstacleTrig = True) \<^bold>& (obstacle\<^bold>!InOut.in \<rightarrow> Skip))
      ) ;; X)
    )"

definition "InputEventBuffers = Obstacle_Buffer"

subsubsection \<open> Environment Main Action \<close>

definition
  "EnvironmentLoop = 
    stepTimer := 0 ;;
    (\<mu> X.
      (Movement \<triangle> ((stepTimer > timeStep) \<^bold>& EnvironmentUpdate)) ;;
      (((stepTimer > timeStep) \<^bold>& Communication) \<triangle>[0] (stepTimer := 0)) ;;
      X
    )"

definition "triggerChannels = \<lbrace>obstacleTriggered\<rbrace>"

definition 
  "Environment = 
    (pos, linVel, linAccel, orient, angVel) := (V[0, 0], 0, 0, V[0, 0], 0) ;;
    (EnvironmentLoop \<lbrakk> triggerChannels \<rbrakk> InputEventBuffers)"

subsection \<open> Mapping \<close>

recursive where 
  "MoveCall = 
    moveCall\<^bold>?(ls,as) \<rightarrow> 
    getRobotAngles\<^bold>?yaw \<rightarrow> 
    setRobotVelocity\<^bold>!V[ls * sin yaw, ls * cos yaw] \<rightarrow> 
    setRobotAngularVelocity\<^bold>!as \<rightarrow> 
    MoveCall"

definition "Move_Operation_Mapping = MoveCall"

recursive where 
  "StopEvent = 
    stop\<^bold>.out \<rightarrow> 
    setRobotVelocity\<^bold>!V[0, 0] \<rightarrow> 
    setRobotAngularVelocity\<^bold>!0 \<rightarrow> 
    StopEvent"

definition "Stop_Output_EventMapping = StopEvent"

hide_const (open) Mapping

definition "Mapping = Move_Operation_Mapping \<interleave> Stop_Output_EventMapping"

subsection \<open> System Composition \<close>

definition "getSetChannels = \<lbrace>
  getRobotPosition, getRobotVelocity, getRobotAcceleration,
  getRobotAngles, getRobotAngularVelocity, getRobotAngularAcceleration,
  setRobotVelocity, setRobotAcceleration,
  setRobotAngularVelocity, setRobotAngularAcceleration
\<rbrace>"

definition "RoboWorld = (Environment \<lbrakk> getSetChannels \<rbrakk> Mapping) \<Zhide> getSetChannels"

end