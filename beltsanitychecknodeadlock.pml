chan feedbelt = [5] of {bool};
bool feedbelt_sensor_triggered;

// #define deadlock 1

#ifndef deadlock
proctype feedbelt_motor()
{
  progress: do
  :: if
     :: atomic { full(feedbelt) -> feedbelt?<feedbelt_sensor_triggered>;
       if
       :: !feedbelt_sensor_triggered -> feedbelt ?_; printf("blank discard\n")
       :: else -> skip; printf("skip\n")
       fi }
     :: atomic { nfull(feedbelt) -> feedbelt ! false; printf("filling\n")}
     fi
  od
}
#else
proctype feedbelt_motor()
{
  progress: do
  :: if
     :: atomic { full(feedbelt) -> feedbelt?<feedbelt_sensor_triggered>;
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

init {
  run feedbelt_motor();
  feedbelt!false;
  feedbelt!false;
  feedbelt!false;
  feedbelt!false;
  feedbelt!false;
  
  run writer();
  run reader();
}

