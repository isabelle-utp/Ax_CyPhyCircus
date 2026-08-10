section \<open> RoboWorld CyPhyCircus Semantics \<close>

theory Ranger_RoboWorld
  imports "Axiomatic_CyPhyCircus.Ax_CyPhyCircus"
begin

subsection \<open> Channels \<close>

datatype InOut = "in" | "out"

chantype RangerChan =   
  getRobotPosition            :: "real \<times> real"
  getRobotVelocity            :: "real \<times> real"
  getRobotAcceleration        :: "real \<times> real"
  getRobotAngles              :: "real"
  getRobotAngularVelocity     :: "real"
  getRobotAngularAcceleration :: "real"
  setRobotVelocity            :: "real \<times> real"
  setRobotAcceleration        :: "real \<times> real"
  setRobotAngularVelocity     :: real
  setRobotAngularAcceleration :: real
  obstacle                    :: InOut
  stop                        :: InOut
  moveCall                    :: "real \<times> real"
  obstacleTriggered           :: bool

subsection \<open> Environment \<close>

consts
  step              :: real
  obstaclePositions :: "(real \<times> real) set"
  collisionRadius   :: real
  detectionRadius   :: real

subsubsection \<open> Environment State \<close>

alphabet EnvironmentState = 
  pos    :: "real \<times> real"
  vel    :: "real \<times> real"
  acc    :: "real \<times> real"
  ang    :: real
  angVel :: real
  angAcc :: real
  time   :: real

subsubsection \<open> Robot Movement \<close>

definition 
  "RobotMovement = 
    [\<Lambda> pos` = vel, vel` = acc, ang` = angVel, angVel` = angAcc]
    \<triangle>\<^sub>p ((\<exists> obs \<in> obstaclePositions. norm (pos - obs) < collisionRadius) \<and> time > step)"

subsubsection \<open> Update Actions that interrupt Robot Movement \<close>

definition
  "CollisionDetection = 
    ((\<exists> obs \<in> obstaclePositions. norm (pos - obs) < collisionRadius) \<^bold>&
      (vel, acc) := ((0, 0), (0, 0)))
    \<box> 
    ((\<not> (\<exists> obs \<in> obstaclePositions. norm (pos - obs) < collisionRadius)) \<^bold>&
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
definition "GetAcceleration = getRobotAcceleration\<^bold>!acc \<rightarrow> Skip"
definition "GetAngles = getRobotAngles\<^bold>!ang \<rightarrow> Skip"
definition "GetAngularVel = getRobotAngularVelocity\<^bold>!angVel \<rightarrow> Skip"
definition "GetAngularAcc = getRobotAngularAcceleration\<^bold>!angAcc \<rightarrow> Skip"

definition "SetVelocity = setRobotVelocity\<^bold>?newVel \<rightarrow> vel := newVel"
definition "SetAcceleration = setRobotAcceleration\<^bold>?newAcc \<rightarrow> acc := newAcc"
definition "SetAngularVel = setRobotAngularVelocity\<^bold>?newAngVel \<rightarrow> angVel := newAngVel"
definition "SetAngularAcc = setRobotAngularAcceleration\<^bold>?newAngAcc \<rightarrow> angAcc := newAngAcc"

definition 
  "GetSetVariables = 
    GetPosition \<interleave> GetVelocity \<interleave> GetAcceleration \<interleave> 
    GetAngles \<interleave> GetAngularVel \<interleave> GetAngularAcc \<interleave> 
    SetVelocity \<interleave> SetAcceleration \<interleave> SetAngularVel \<interleave> SetAngularAcc"

recursive where "Communication = InputTriggers ; (GetSetVariables ; Communication)"

subsubsection \<open> Input Event Buffers \<close>

definition
  "Obstacle_Buffer = 
    (var obstacleTrig :: bool. 
      obstacleTrig := False ;
      (\<mu> X.(  
        obstacleTriggered\<^bold>?b \<rightarrow> (obstacleTrig := b)
        \<box>
        ((obstacleTrig = True) \<^bold>& (obstacle\<^bold>!InOut.in \<rightarrow> Skip))
      ) ; X)
    )"

definition "InputEventBuffers = Obstacle_Buffer"

subsubsection \<open> Environment Main Action \<close>

definition
  "EnvironmentLoop = 
    time := 0 ; 
    (\<mu> X.
      (RobotMovement \<triangle> ((time > step) \<^bold>& EnvironmentUpdate)) ; 
      (((time > step) \<^bold>& Communication) \<triangle>[0] (time := 0)) ;
      X
    )"

definition "triggerChannels = \<lbrace>obstacleTriggered\<rbrace>"

definition 
  "Environment = 
    (pos, vel, acc, ang, angVel, angAcc) := ((0,0), (0,0), (0,0), 0, 0, 0) ;
    (EnvironmentLoop \<lbrakk> triggerChannels \<rbrakk> InputEventBuffers)"

subsection \<open> Mapping \<close>

recursive where 
  "MoveCall = 
    moveCall\<^bold>?(ls,as) \<rightarrow> 
    getRobotAngles\<^bold>?yaw \<rightarrow> 
    setRobotVelocity\<^bold>!(ls * sin yaw, ls * cos yaw) \<rightarrow> 
    setRobotAngularVelocity\<^bold>!as \<rightarrow> 
    MoveCall"

definition "Move_Operation_Mapping = MoveCall"

recursive where 
  "StopEvent = 
    stop\<^bold>.out \<rightarrow> 
    setRobotVelocity\<^bold>!(0, 0) \<rightarrow> 
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