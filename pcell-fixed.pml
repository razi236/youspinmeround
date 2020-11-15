// This is a simplified model of the prodution cell
// certain actions are assumed encapsulated by states
// i.e. rotation and elevation of the table is simply
// entering the needed configuration.
//
// Run with spin -search -l pcell.pml to check for non-progress cycle

#define FEEDBELT_CAPACITY 5
#define DEPOSITBELT_CAPACITY 5

// Traveling crane states
mtype:crane = {
  move_to_feedbelt,
  move_to_depositbelt,
  at_feedbelt,
  at_depositbelt
};

// Elevating rotary table, combining rotation and elevation
mtype:table = {
  enter_load_by_feedbelt,
  enter_unload_to_arm1,
  load_by_feedbelt,
  unload_to_arm1
};

// Robot
mtype:robot = {
  enter_arm1_at_table,
  enter_arm1_at_press,
  enter_arm2_at_press,
  enter_arm2_at_depositbelt,
  arm1_at_table,
  arm1_at_press,
  arm2_at_press,
  arm2_at_depositbelt  
}

mtype:press = {
  load_by_arm1,
  pressing,
  unload_by_arm2
}

chan feedbelt = [FEEDBELT_CAPACITY] of {bool};
chan depositbelt = [DEPOSITBELT_CAPACITY] of {bool};
mtype:table table_state;
mtype:robot robot_state;
mtype:press press_state;
mtype:crane crane_state;

bool on_table;

bool feedbelt_sensor_triggered;
bool depositbelt_sensor_triggered;
bool in_gripper;
bool in_arm1;
bool in_arm2;
bool in_press;

// If we are to model the belt with a channel as discussed
// then an "axiom" is that the channel must always be full
// for example if the capacity of the feedbelt is 5 then
// a channel of [1,0,0] is not a valid representation of the belt
// only [1,0,0,0,0] would be, i.e. the channel must always be full.
// I think a good compromise here is that at least a belt should
// only allow interaction in a valid state(i.e. full).

// Progress markers are needed in the belts to mark the cycle of
// empty belts spinning as progress or simply the waiting when the
// sensor is triggered.

// alternative implementation of the sensors could be as shown below,
// in which case we can remove the need to set bools  
// 
// #define feedbelt_sensor_triggered (feedbelt?[true])
// #define depositbelt_sensor_triggered (depositbelt?[true])

proctype feedbelt_motor()
{
  progress: do
  :: if
     :: atomic { full(feedbelt) -> feedbelt?<feedbelt_sensor_triggered>;
       if
       :: !feedbelt_sensor_triggered -> feedbelt ?_
       :: else -> skip;
       fi }
     :: atomic { full(feedbelt) -> feedbelt ! false }
     fi
  od
}

proctype depositbelt_motor()
{
  progress: do
  :: if
     :: atomic { full(depositbelt) -> depositbelt?<depositbelt_sensor_triggered>;
       if
       :: !depositbelt_sensor_triggered -> depositbelt ?_
       :: else -> skip
       fi }
     :: atomic { nfull(depositbelt) -> depositbelt ! false }
     fi 
  od
}

proctype table()
{
  do 
  :: (table_state == load_by_feedbelt &&
      !on_table &&
      feedbelt_sensor_triggered)             -> progress: feedbelt?on_table
  :: (table_state == load_by_feedbelt &&
      on_table)                              -> table_state = enter_unload_to_arm1
  :: (table_state == enter_unload_to_arm1)   -> table_state = unload_to_arm1
  :: atomic {
       (table_state == unload_to_arm1 &&
        on_table &&
        robot_state == arm1_at_table)        -> on_table = false; in_arm1 = true }
  :: (table_state == unload_to_arm1 &&
      !on_table)                             -> table_state = enter_load_by_feedbelt
  :: (table_state == enter_load_by_feedbelt) -> table_state = load_by_feedbelt
  od
} 

// First sequence(starting sequence 1. & 2. / only sequence for 1 item ):
// 1. load arm1 from table
// 2. place item in arm1 in press
// 3. load arm2 from press
// 4. unload arm2 in depositbelt, goto 1
//
// Second sequence(loads both arms):
// Precondition: step 1. and step 2. from first sequence have occured
// 1. load arm1 from table
// 2. load arm2 from press
// 3. unload arm2 in depositbelt
// 4. unload arm1 in press, goto 1.
//
// For now the first sequence is implemented

proctype robot() {
  do
  ::(robot_state == enter_arm1_at_table &&
     !in_arm1 &&
     table_state == unload_to_arm1)                   -> robot_state = arm1_at_table
  :: (robot_state == arm1_at_table &&
      !in_arm1 &&
      table_state == unload_to_arm1 &&
      on_table)                                       -> atomic { in_arm1 = true; on_table = false }
  :: (robot_state == arm1_at_table &&
      in_arm1)                                        -> robot_state = enter_arm1_at_press
  :: (robot_state == enter_arm1_at_press &&
      press_state == load_by_arm1 &&
      in_arm1)                                        -> robot_state = arm1_at_press
  :: (robot_state == arm1_at_press &&
      in_arm1)                                        -> atomic { in_arm1 = false; in_press = true }
  :: (robot_state == arm1_at_press &&
      !in_arm1)                                       -> robot_state = enter_arm2_at_press
  :: (robot_state == enter_arm2_at_press &&
      press_state == unload_by_arm2 &&
      in_press)                                       -> robot_state = arm2_at_press
  :: (robot_state == arm2_at_press)                   -> atomic { in_arm2 = true; in_press = false;
                                                                  robot_state = enter_arm2_at_depositbelt }
  :: (robot_state == enter_arm2_at_depositbelt)       -> robot_state = arm2_at_depositbelt
  :: (robot_state == arm2_at_depositbelt && in_arm2)  -> atomic { depositbelt ! true; in_arm2 = false }
  :: (robot_state == arm2_at_depositbelt && !in_arm2) -> progress: robot_state = enter_arm1_at_table
  od  
}

// Initial configuration at_depositbelt and in_gripper = false
// just endlessly picks sheats from depositbelt and places them in feedbelt
proctype crane()
{
  do
  :: (crane_state == move_to_feedbelt)    -> crane_state = at_feedbelt
  :: (crane_state == move_to_depositbelt) -> crane_state = at_depositbelt
  :: (crane_state == at_feedbelt &&
      !in_gripper)                        -> crane_state = move_to_depositbelt
  :: (crane_state == at_feedbelt &&
      in_gripper)                         -> atomic { feedbelt ! true; in_gripper = false }
  :: (crane_state == at_depositbelt &&
      !in_gripper &&
      depositbelt_sensor_triggered)       -> depositbelt?in_gripper
  :: (crane_state == at_depositbelt &&
      in_gripper)                         -> progress: crane_state = move_to_feedbelt
  od
}

// Initial configuration load_by_arm1 and in_press = false
proctype press()
{
  do
  :: (press_state == load_by_arm1 && in_press)    -> press_state = pressing
  :: (press_state == pressing)                    -> press_state = unload_by_arm2
  :: (press_state == unload_by_arm2 && !in_press) -> progress: press_state = load_by_arm1
  od
}

init
{
    table_state = load_by_feedbelt;
    robot_state = arm1_at_table;
    press_state = load_by_arm1;
    crane_state = at_depositbelt;

    // belt configuration
    feedbelt ! true;
    feedbelt ! false;
    feedbelt ! false;
    feedbelt ! false;
    feedbelt ! false;

    depositbelt ! false;
    depositbelt ! false;
    depositbelt ! false;
    depositbelt ! false;
    depositbelt ! false;

    
    //feedbelt_sensor_triggered = false;
    //depositbelt_sensor_triggered = false;
    on_table = false;
    in_arm1 = false;
    in_arm2 = false;
    in_gripper = false;
    in_press = false;

    atomic {
      run feedbelt_motor();
      run depositbelt_motor();
      run table();
      run robot();
      run press();
      run crane();
    }
}


// To check only this do "spin -search -ltl advance_from_table pcell.pml"
ltl advance_from_table {(<>on_table -> <>in_arm1 )}


// Liveness checks

ltl piece_on_table {([]<>on_table)}
ltl piece_in_arm1 {([]<>in_arm1)}
ltl piece_in_arm2 {([]<>in_arm2)}
ltl piece_in_gripper {([]<>in_gripper)}
ltl piece_in_press {([]<>in_press)}
ltl piece_on_feedbelt_sensor {([]<>feedbelt_sensor_triggered)}
ltl piece_on_depositbelt_sensor {([]<>depositbelt_sensor_triggered)}


ltl piece_somewhere { ([]<>on_table &&
                       []<>feedbelt_sensor_triggered &&
                       []<>depositbelt_sensor_triggered &&
                       []<>in_gripper &&
                       []<>in_arm1 &&
                       []<>in_arm2 &&
                       []<>in_press )}
