chan feedbelt = [5] of {bool};
bool feedbelt_sensor_triggered;

// #define deadlock 1

#ifndef deadlock
active proctype feedbelt_motor()
{
  progress: do
  :: atomic {
     if
     :: full(feedbelt) -> feedbelt?<feedbelt_sensor_triggered>;
       if
       :: !feedbelt_sensor_triggered -> feedbelt ?_; printf("blank discard\n")
       :: else -> skip; printf("skip\n")
       fi
     :: nfull(feedbelt) -> feedbelt ! false; printf("filling\n")
     fi
     }
  od
}
#else
active proctype feedbelt_motor()
{
  progress: do
  :: if
     :: full(feedbelt) -> atomic { feedbelt?<feedbelt_sensor_triggered>;
       if
       :: !feedbelt_sensor_triggered -> feedbelt ?_; printf("blank discard\n")
       :: else -> skip; printf("skip\n")
       fi }
     :: nfull(feedbelt) -> feedbelt ! false; printf("filling\n")
     fi
  od
}
#endif


active proctype writer()
{

 do
 :: true -> feedbelt!true; printf("writer writes\n")
 od
}

active proctype reader()
{

 do
 :: feedbelt_sensor_triggered -> feedbelt?_ ; printf("reader reads\n")
 od
}


