#define FEEDBELT_CAPACITY 3
bool feedbelt_sensor_triggered;
chan feedbelt = [FEEDBELT_CAPACITY] of {bool};
proctype feedbelt_motor()
{
  progress: do
  
	:: if
     	   :: full(feedbelt) -> atomic { feedbelt?<feedbelt_sensor_triggered>;
       	      if
		:: !feedbelt_sensor_triggered -> feedbelt ?_;
       		:: else -> skip;
       		fi
		}
     	   ::  nfull(feedbelt) -> feedbelt ! false;
	fi
     
  od
}
init
{
atomic {
	feedbelt ! true;
    	feedbelt ! false;
    	feedbelt ! false;
	feedbelt_sensor_triggered = true;
	}
	run feedbelt_motor();
	
}
