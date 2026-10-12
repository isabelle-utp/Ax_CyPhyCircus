theory Ranger_Kinematics
  imports "Axiomatic_CyPhyCircus.Ax_CyPhyCircus"
begin

text \<open> A version of the ranger using a unicycle kinematics model. \<close>

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

subsection \<open> Channels \<close>

datatype InOut = "inp" | "out"

chantype RobotChan =   
  getRobotPosition            :: "real vec[2]"
  getRobotVelocity            :: "real"
  getRobotAcceleration        :: "real"
  getRobotOrientation         :: "real vec[2]"
  getRobotAngularVelocity     :: "real"
  getRobotSetpoint            :: "real"
  \<comment> \<open> We can only set monitored variables \<close>
  setRobotAcceleration        :: "real"
  setRobotAngularVelocity     :: "real"
  setRobotSetpoint            :: "real"
  obstacle                    :: "InOut"
  stop                        :: "InOut"
  moveCall                    :: "real \<times> real"
  obstacleTriggered           :: "bool"

subsection \<open> State and Channels \<close>

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

expression Assumptions is 
  "maxBrake > 0 \<and> maxVel > 0 \<and> maxAngVel > 0 \<and> timeStep > 0 \<and>
   collisionRadius > 0 \<and> detectionRadius > 0"

alphabet EnvironmentState = 
  accel      :: real
  pos        :: "real vec[2]"
  orient     :: "real vec[2]"
  linVel     :: real
  setpoint   :: real
  angVel     :: real
  angRadius  :: real
  stepTimer  :: real
  targetTrig :: bool

expression EnvironmentState_inv is 
  "0 \<le> linVel \<and> linVel \<le> maxVel \<and> stepTimer \<le> timeStep"
  
subsection \<open> Kinematics \<close>

definition Movement :: "(RobotChan, EnvironmentState) cyphyaction" where
"Movement = [\<Lambda> pos` = linVel *\<^sub>R orient, linVel` = accel
            ,  orient` = angVel *\<^sub>R rot90(orient), accel` = 0
            ,  angVel` = (if angRadius = 0 then 0 else accel / angRadius)
            ,  stepTimer` = 1 
            | 0 \<le> linVel \<and> linVel \<le> maxVel \<and> stepTimer \<le> timeStep]"

subsubsection \<open> Update Actions that interrupt Robot Movement \<close>

definition "EnvironmentUpdate = (linVel = setpoint) \<^bold>& accel := 0
                              \<box> (linVel \<noteq> setpoint) \<^bold>& Skip"

subsubsection \<open> Communication Actions that occur on the time step \<close>

definition
  "Obstacle_InEventMapping = 
    ((\<exists> obs \<in> obstaclePositions. \<parallel>pos - obs\<parallel> < detectionRadius) \<^bold>&
      (obstacleTriggered\<^bold>!True \<rightarrow> Skip))
    \<box>
    ((\<not> (\<exists> obs \<in> obstaclePositions. \<parallel>pos - obs\<parallel> < detectionRadius)) \<^bold>&
      (obstacleTriggered\<^bold>!False \<rightarrow> Skip))"

definition "InputTriggers = Obstacle_InEventMapping"

definition "GetPosition = getRobotPosition\<^bold>!pos \<rightarrow> Skip"
definition "GetVelocity = getRobotVelocity\<^bold>!linVel \<rightarrow> Skip"
definition "GetAcceleration = getRobotAcceleration\<^bold>!accel \<rightarrow> Skip"
definition "GetOrientation = getRobotOrientation\<^bold>!orient \<rightarrow> Skip"
definition "GetAngularVel = getRobotAngularVelocity\<^bold>!angVel \<rightarrow> Skip"

definition "SetAcceleration = setRobotAcceleration\<^bold>?newAcc \<rightarrow> accel := newAcc"
definition "SetAngularVel = setRobotAngularVelocity\<^bold>?newAngVel \<rightarrow> angVel := newAngVel"

definition 
  "GetSetVariables = 
    GetPosition \<interleave> GetVelocity \<interleave> GetAcceleration \<interleave> 
    GetOrientation \<interleave> GetAngularVel \<interleave> SetAcceleration \<interleave> 
    SetAngularVel"

recursive where "Communication = InputTriggers ;; (GetSetVariables ;; Communication)"

subsubsection \<open> Input Event Buffers \<close>

definition
  "Obstacle_Buffer = 
    (var obstacleTrig :: bool. 
      obstacleTrig := False ;;
      (\<mu> X. (  
        obstacleTriggered\<^bold>?b \<rightarrow> (obstacleTrig := b)
        \<box>
        ((obstacleTrig = True) \<^bold>& (obstacle\<^bold>.inp \<rightarrow> Skip))
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
    (pos, linVel, accel, orient, angVel) := (V[0, 0], 0, 0, V[0, 0], 0) ;;
    (EnvironmentLoop \<lbrakk> triggerChannels \<rbrakk> InputEventBuffers) \<Zhide> triggerChannels "

subsection \<open> Mapping \<close>

text \<open> The move operation updates the the setpoint, and changes the acceleration
  to increase or decrease the velocity. \<close>

recursive where 
  "MoveCall = 
    (moveCall\<^bold>?(ls,as) \<rightarrow> 
     setRobotAngularVelocity\<^bold>!as \<rightarrow>
     setRobotSetpoint\<^bold>?ls \<rightarrow>
     getRobotVelocity\<^bold>?vs \<rightarrow>
       ((ls > vs)  \<^bold>& setRobotAcceleration\<^bold>!maxAccel \<rightarrow> Skip
       \<box> (ls < vs) \<^bold>& setRobotAcceleration\<^bold>!(- maxBrake) \<rightarrow> Skip
       \<box> (ls = vs) \<^bold>& Skip
       )) ;;
    MoveCall"

definition "Move_Operation_Mapping = MoveCall"

recursive where 
  "StopEvent = 
    stop\<^bold>.out \<rightarrow> 
    setRobotSetpoint\<^bold>!0 \<rightarrow> 
    setRobotAcceleration\<^bold>!(- maxBrake) \<rightarrow>
    setRobotAngularVelocity\<^bold>!0 \<rightarrow> 
    StopEvent"

definition "Stop_Output_EventMapping = StopEvent"

hide_const (open) Mapping

definition "Mapping = Move_Operation_Mapping \<interleave> Stop_Output_EventMapping"

subsection \<open> System Composition \<close>

definition "getSetChannels = \<lbrace>
  getRobotPosition, getRobotVelocity, getRobotAcceleration,
  getRobotOrientation, getRobotAngularVelocity,
  setRobotAcceleration, setRobotSetpoint, setRobotAngularVelocity
\<rbrace>"

definition "RoboWorld = (Environment \<lbrakk> getSetChannels \<rbrakk> Mapping) \<Zhide> getSetChannels"

end