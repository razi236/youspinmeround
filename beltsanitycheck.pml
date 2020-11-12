chan feedbelt = [5] of {bool};
bool feedbelt_sensor_triggered;
active proctype feedbelt_motor()
{
  do
  :: if
     :: full(feedbelt) -> progress: atomic { feedbelt?<feedbelt_sensor_triggered>;
       if
       :: !feedbelt_sensor_triggered -> feedbelt ?_;
       :: else -> skip;
       fi }
     :: nfull(feedbelt) -> feedbelt ! false;
     fi
  od
}

active proctype adder()
{

 do
 :: true -> feedbelt!true
 od
}


